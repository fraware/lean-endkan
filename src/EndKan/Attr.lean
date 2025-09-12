import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import EndKan.Kan.BeckChevalley

namespace EndKan.Attr

open CategoryTheory
open CategoryTheory.Limits
open Lean Elab Command

/-- Attribute for registering Kan squares -/
syntax (name := kanSquare) "kan.square" : attr

/-- Metadata for Kan squares -/
structure KanSquareData where
  square : BeckChevalley.Square
  isPullback : Bool
  isFullyFaithful : Bool
  isExact : Bool
  derivedLemma : Name
  tacticRecipe : Name

/-- Registry for Kan squares -/
def kanSquareRegistry : IO.Ref (Std.HashMap Name KanSquareData) := IO.mkRef {}

/-- Register a Kan square -/
def registerKanSquare (name : Name) (data : KanSquareData) : IO Unit := do
  let registry ← kanSquareRegistry.get
  kanSquareRegistry.set (registry.insert name data)

/-- Get Kan square data -/
def getKanSquareData (name : Name) : IO (Option KanSquareData) := do
  let registry ← kanSquareRegistry.get
  return registry.find? name

/-- Check if a Kan square is registered -/
def isKanSquareRegistered (name : Name) : IO Bool := do
  let registry ← kanSquareRegistry.get
  return registry.contains name

/-- List all registered Kan squares -/
def listKanSquares : IO (List Name) := do
  let registry ← kanSquareRegistry.get
  return registry.toList.map (·.1)

/-- Clear all registered Kan squares -/
def clearKanSquares : IO Unit := do
  kanSquareRegistry.set {}

/-- Attribute handler for Kan squares -/
def kanSquareAttrHandler : AttributeHandler where
  add name _ _ := do
    let data : KanSquareData := {
      square := BeckChevalley.Square.mk (by simp)
      isPullback := true
      isFullyFaithful := true
      isExact := true
      derivedLemma := name
      tacticRecipe := name
    }
    registerKanSquare name data
  apply name _ _ := do
    let data : KanSquareData := {
      square := BeckChevalley.Square.mk (by simp)
      isPullback := true
      isFullyFaithful := true
      isExact := true
      derivedLemma := name
      tacticRecipe := name
    }
    registerKanSquare name data

/-- Register the Kan square attribute -/
initialize kanSquareAttr : Attribute where
  name := `kan.square
  descr := "Register a commutative square with hypotheses that justify Beck-Chevalley"
  add := kanSquareAttrHandler.add
  apply := kanSquareAttrHandler.apply

/-- Macro for defining Kan squares -/
syntax "def_kan_square " ident " : " term " := " term : command

/-- Elaborator for Kan square definitions -/
elab_rules : command
  | `(def_kan_square $name : $type := $proof) => do
    let cmd ← `(def $name : $type := $proof)
    elabCommand cmd
    let attrCmd ← `(attribute [kan.square] $name)
    elabCommand attrCmd

/-- Macro for defining Kan squares with explicit data -/
syntax "def_kan_square_data " ident " : " term " := " term " where" " isPullback := " term " isFullyFaithful := " term " isExact := " term : command

/-- Elaborator for Kan square definitions with data -/
elab_rules : command
  | `(def_kan_square_data $name : $type := $proof where isPullback := $isPullback isFullyFaithful := $isFullyFaithful isExact := $isExact) => do
    let cmd ← `(def $name : $type := $proof)
    elabCommand cmd
    let attrCmd ← `(attribute [kan.square] $name)
    elabCommand attrCmd
    let data : KanSquareData := {
      square := BeckChevalley.Square.mk (by simp)
      isPullback := true
      isFullyFaithful := true
      isExact := true
      derivedLemma := name
      tacticRecipe := name
    }
    registerKanSquare name data

end EndKan.Attr
