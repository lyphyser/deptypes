# deptypes

[![crate](https://img.shields.io/crates/v/deptypes.svg)](https://crates.io/crates/deptypes)
[![documentation](https://docs.rs/deptypes/badge.svg)](https://docs.rs/deptypes)

An implementation of dependent types for Rust by lifting values to the type level.

It's mostly a proof of concept, although it can be used in practice, but you might need to extend it and add missing functionality as needed.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
deptypes = "0.1"
```
## How does it work?

The crate defines a `Term` trait for Values, and a `Value<T>` type that carries the value of a term.

This allows to form zero-sized term types like `Add<A, B>` representing the sum of two Values.

Variables are implemented by leveraging the `generativity` crate to define a `Var<'a, T>` term that represents a variable and such that a `Value<Var<'a, T>>` can only be instantiated once, thus guaranteeing that the value of a variable is always the same (for each time the region it's used in is run).

A `ValueEq<A, B>` value encodes a proof that the Values `A` and `B` have the same value, and allows to transmute `Value<A>` into `Value<B>`.

Several facilities are provided on top of these basic features, such as Peano-like Values for integer, dependent range-limited integers, data dependent pair and Result, dependent Vec, as well as basic tools for theorem proving, like notions of total functions, inhabited types, tools to create a combine equality proofs, axioms and theorems for integers.

Note that unlike dependently typed languages, this crate uses a lot of asserted axioms, since proving things by induction is very unwieldy although possible, and also requires to either assert the totality and purity of Rust functions or build a way
to encode total pure functions at the type level and execute them (currently not done, you are welcome to try).

The set of provided facilities is not really intended to be complete at the moment.

## Features

The `std` feature enables the standard library, the `nightly` feature enable parts of the crate that need nightly, consisting of the `gat` and `never` features requiring GATs and the never type specifically.

## Example

This is an example of guaranteed non-panicing indexing of multiple arrays, as well as encapsulation of dependent types using dependent pairs.

```rust
use deptypes::{term::{Term, ValueEq, Def}, fin::Fin, uint::{Succ, add::a_lt_s_a}, vec::DVec, DPair, transmutable::vec_transm, make_guard};
use std::vec::Vec;

// repr C to support transmute
#[repr(C)]
struct DWorld<NumEntities: Term<Type = usize>, NumMonsters: Term<Type = usize>> {
    // vectors of num_entities positions and velocities
    position: DVec<f64, NumEntities>,
    velocity: DVec<f64, NumEntities>,

    // vector of numbers less than num_entities representing entities that are a monster
    monsters: DVec<Fin<NumEntities>, NumMonsters>,
    smart_monsters: Vec<Fin<NumMonsters>>
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
        let monsters = DVec::transm(Fin::transm(a_lt_s_a().le()), ValueEq::refl()).coerce(self.monsters);
        let smart_monsters = self.smart_monsters;

        DWorld {position, velocity, monsters, smart_monsters}
    }

    fn add_monster(self, entity: Fin<NumEntities>) -> DWorld<NumEntities, Succ<NumMonsters>> {
        let position = self.position;
        let velocity = self.velocity;
        // use fact that a < Succ(a) => a <= Succ(a) => Fin<a> transm to Fin<Succ(a)> to coerce monsters
        let monsters = self.monsters.push(entity);
        let smart_monsters = vec_transm(Fin::transm(a_lt_s_a().le())).coerce(self.smart_monsters);

        DWorld {position, velocity, monsters, smart_monsters}
    }

    fn add_smart_monster(&mut self, monster: Fin<NumMonsters>) {
        self.smart_monsters.push(monster);
    }
}

DPair! {
    // these are unsafe because we must ensure that it is valid to transmute the types between terms
    unsafe type World1<NumEntities: Term<Type = usize>> = (usize, DWorld<NumEntities>);
    unsafe type World0 = (usize, World1);
}

pub struct EntityId(usize);
pub struct EntityIdInvalidError;

pub struct MonsterId(usize);
pub struct MonsterIdInvalidError;

#[derive(Default)]
pub struct World(World0);

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
        let (num_entities, world1) = core::mem::replace(&mut self.0, World0::default()).into_inner(g);
        make_guard!(g);
        let (num_monsters, world) = world1.into_inner(g);

        let world = world.add_entity(position, velocity);

        self.0 = World0::new(Succ(num_entities), World1::new(num_monsters, world));
        EntityId(num_entities.into_inner())
    }

    pub fn add_monster(&mut self, entity: EntityId) -> Result<MonsterId, EntityIdInvalidError> {
        make_guard!(g);
        let (num_entities, world1) = core::mem::replace(&mut self.0, World0::default()).into_inner(g);
        make_guard!(g);
        let (num_monsters, world) = world1.into_inner(g);

        let world = world.add_monster(Fin::from(num_entities, entity.0).ok_or(EntityIdInvalidError)?);

        self.0 = World0::new(num_entities, World1::new(Succ(num_monsters), world));
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
