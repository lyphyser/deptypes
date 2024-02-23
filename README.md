# deptypes

[![crate](https://img.shields.io/crates/v/deptypes.svg)](https://crates.io/crates/deptypes)
[![documentation](https://docs.rs/deptypes/badge.svg)](https://docs.rs/deptypes)

An implementation of dependent types for Rust by lifting values to the type level.

It can be used in practice for relatively simple applications like vector types depending on the vector length, but you might need to extend it and add missing functionality as needed for more complex usae cases.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
deptypes = "0.2"
```

## How does it work?

The crate defines a `Term` trait to represent expressions lifted to the type level, and a `Value<T: Term>` type that carries the value of a term.

This allows to form zero-sized term types like `Succ<A>` representing A + 1 and `Add<A, B>` representing the sum of two Values.

We can then form, for example, `DLVec<i32, Var<'a, usize>>` and `DLVec<i32, Succ<Var<'a, usize>>>`, which are two vectors of i32s where the second one is guaranteed to be always one item longer than the first; 

`Var<'a, T>` represents variables, implemented by leveraging the `generativity` crate to define a term such that `Value<Var<'a, T>>` can only be instantiated once, thus guaranteeing that the value of a variable is always the same (for each time the region it's used in is run).

A `ValueEq<A, B>` value encodes a proof that the Values `A` and `B` have the same value, and allows to safely transmute `Value<A>` into `Value<B>`. For instance, the `uint_as_succ ` function takes an unsigned integer and a `Guard<'a>` and either returns a proof that it is zero `ValueEq<A, Zero<A::Type>>` or the value of its predecessor expressed as a variable `Value<Var<'a, A::Type>>` and a proof that the input number is its successor `ValueEq<A, Succ<Var<'a, A::Type>>>`.`

Several facilities are provided on top of these basic features, such as Peano-like terms for integers, dependent range-limited integers, data dependent pair and Result, dependent Vec, tools to create and combine equality proofs, axioms and theorems for integers and booleans.

Note that unlike dependently typed languages, this crate uses several asserted axioms, since proving things by induction is very unwieldy although possible, and also would require to either assert the totality and purity of Rust functions or build a way to encode total pure functions at the type level.

The set of provided facilities is quite basic at the moment.

## Features

The `std` feature enables the standard library, the `nightly` feature enable parts of the crate that need nightly, currently consisting of the `never` features requiring the never type.

## Example

This is an example of guaranteed non-panicing indexing of multiple length-dependent vectors, as well as encapsulation of dependent types using dependent pairs.

```rust
use deptypes::{term::{Term, ValueEq, Def}, fin::Fin, int::{Succ, a_lt_s_a}, vec::DVec, pair::DPair, kinds::Term2S, transmutable::{coerce, coerce_vec}, type_eq::refl, make_guard};
use core::marker::PhantomData;
use std::vec::Vec;

#[repr(C)] // to support trasmutation by Term2S::equiv
struct DWorld<NumEntities: Term<Type = usize>, NumMonsters: Term<Type = usize>> {
    // vectors of num_entities positions and velocities
    position: DVec<f64, NumEntities>,
    velocity: DVec<f64, NumEntities>,

    // vector of numbers less than num_entities representing entities that are a monster
    monsters: DVec<Fin<NumEntities>, NumMonsters>,
    smart_monsters: Vec<Fin<NumMonsters>>
}

struct DWorldFamily<NumEntities>(PhantomData<NumEntities>);

unsafe impl<NumEntities: Term<Type = usize>> Term2S<usize> for DWorldFamily<NumEntities>
{
    type Type<NumMonsters: Term<Type = usize>> = DWorld<NumEntities, NumMonsters>;
}

// this could be derived if deriving used proper bounds
impl Default for DWorld<Def<usize>, Def<usize>> {
    fn default() -> Self {
        DWorld {
            position: Default::default(),
            velocity: Default::default(),
            monsters: Default::default(),
            smart_monsters: Default::default()
        }
    }
}

impl<NumEntities: Term<Type = usize>, NumMonsters: Term<Type = usize>> DWorld<NumEntities, NumMonsters> {
    fn add_entity(self, position: f64, velocity: f64) -> DWorld<Succ<NumEntities>, NumMonsters> {
        // coerce all data from depending on Succ<old num_entities> to new num_entities
        let position = self.position.push(position);
        let velocity = self.velocity.push(velocity);
        // use fact that a < Succ(a) => a <= Succ(a) => Fin<a> transm to Fin<Succ(a)> to coerce monsters
        let monsters = coerce(self.monsters, DVec::transm(Fin::transm(a_lt_s_a().le()), refl()));
        let smart_monsters = self.smart_monsters;

        DWorld {position, velocity, monsters, smart_monsters}
    }

    fn add_monster(self, entity: Fin<NumEntities>) -> DWorld<NumEntities, Succ<NumMonsters>> {
        let position = self.position;
        let velocity = self.velocity;
        // use fact that a < Succ(a) => a <= Succ(a) => Fin<a> transm to Fin<Succ(a)> to coerce monsters
        let monsters = self.monsters.push(entity);
        let smart_monsters = coerce_vec(self.smart_monsters, Fin::transm(a_lt_s_a().le()));

        DWorld {position, velocity, monsters, smart_monsters}
    }

    fn add_smart_monster(&mut self, monster: Fin<NumMonsters>) {
        self.smart_monsters.push(monster);
    }
}

struct DPairDWorldFamily;

unsafe impl Term2S<usize> for DPairDWorldFamily
{
    type Type<NumEntities: Term<Type = usize>> = DPair<usize, DWorldFamily<NumEntities>>;
}

#[derive(Default)]
pub struct World(DPair<usize, DPairDWorldFamily>);

pub struct EntityId(usize);
pub struct EntityIdInvalidError;

pub struct MonsterId(usize);
pub struct MonsterIdInvalidError;

impl World {
    pub fn move_smart_monsters(&mut self, time: f64) {
        make_guard!(g);
        let (_num_entities, world1) = self.0.get_mut(g);
        make_guard!(g);
        let (_num_monsters, world) = world1.get_mut(g);

        for m in world.smart_monsters.iter().copied() {
            // these indexing operations are guaranteed to never fail, thanks to the dependent types!
            let e = world.monsters[m];
            world.position[e] += world.velocity[e] * time;
        }
    }

    pub fn add_entity(&mut self, position: f64, velocity: f64) -> EntityId {
        make_guard!(g);
        let (num_entities, world1) = core::mem::replace(&mut self.0, DPair::default()).into_inner(g);
        make_guard!(g);
        let (num_monsters, world) = world1.into_inner(g);

        let world = world.add_entity(position, velocity);

        self.0 = DPair::new(Succ(num_entities), DPair::new(num_monsters, world));
        EntityId(num_entities.into_inner())
    }

    pub fn add_monster(&mut self, entity: EntityId) -> Result<MonsterId, EntityIdInvalidError> {
        make_guard!(g);
        let (num_entities, world1) = core::mem::replace(&mut self.0, DPair::default()).into_inner(g);
        make_guard!(g);
        let (num_monsters, world) = world1.into_inner(g);

        let world = world.add_monster(Fin::from(num_entities, entity.0).ok_or(EntityIdInvalidError)?);

        self.0 = DPair::new(num_entities, DPair::new(Succ(num_monsters), world));
        Ok(MonsterId(num_monsters.into_inner()))
    }

    pub fn add_smart_monster(&mut self, monster: MonsterId) -> Result<(), MonsterIdInvalidError> {
        make_guard!(g);
        let (_num_entities, world1) = self.0.get_mut(g);
        make_guard!(g);
        let (num_monsters, world) = world1.get_mut(g);

        world.add_smart_monster(Fin::from(*num_monsters, monster.0).ok_or(MonsterIdInvalidError)?);

        Ok(())
    }
}
```

## Changelog

### Version 0.2
General overhaul of the whole codebase.

- Now requires GATs and thus Rust >= 1.66
- Helpers to loop over a dependently-typed stated, so recursion is no longer needed and should no longer be used (since it will overflow the stack)
- Non-essential features moved to deptypes_extra
- type_eq overhauled: now have a TypeNe and no longer uses Uninhabited
- Terms now use checked_*, avoiding overflows, making them sound
- Ops terms now require ConstOps, since non-const ops would make them unsound
- term! only supports fn-like syntax
- DPair is now a struct and no longer a macro
- Arithmetic theorems are now proven using only a small number of axioms
- More arithmetic theorems

### Version 0.1
Initial version