import SubVerso.Examples

-- ANCHOR: ch01_hello_log
import Lean

open Lean

run_cmd
  logInfo m!"Hello, world!"
-- ANCHOR_END: ch01_hello_log

set_option autoImplicit false

-- ANCHOR: ch01_observe_value
run_cmd
  let stage := "elaboration"
  logInfo m!"Now observing: {stage}"
-- ANCHOR_END: ch01_observe_value

-- ANCHOR: ch01_runtime_hello
def main : IO Unit :=
  IO.println "Hello, world!"
-- ANCHOR_END: ch01_runtime_hello

-- ANCHOR: ch01_observation_commands
#check IO.println
#eval 2 + 3
-- ANCHOR_END: ch01_observation_commands

-- ANCHOR: ch01_interpolation
run_cmd
  let language := "Lean"
  let plain : String := s!"Hello, {language}!"
  let message : MessageData := m!"Hello, {language}!"
  logInfo message
-- ANCHOR_END: ch01_interpolation

-- ANCHOR: ch01_split_fields
run_cmd
  let raw := "10,oops,20"
  let fields := raw.splitOn ","
  logInfo m!"fields: {fields}"
-- ANCHOR_END: ch01_split_fields

-- ANCHOR: ch01_name
run_cmd
  let text := "Lean.Meta.mkAppM"
  let name : Name := text.toName
  let parent := name.getPrefix
  logInfo m!"name: {name}; parent: {parent}"
-- ANCHOR_END: ch01_name

-- ANCHOR: ch01_describe_option
def describeNat? (value : Option Nat) : String :=
  match value with
  | some n => s!"found {n}"
  | none => "missing"

#eval describeNat? "42".toNat?
#eval describeNat? "oops".toNat?
-- ANCHOR_END: ch01_describe_option

-- ANCHOR: ch01_anonymous_function
#check (fun field : String => field.toNat?)
-- ANCHOR_END: ch01_anonymous_function

-- ANCHOR: ch01_filter_map
run_cmd
  let fields := "10,oops,20".splitOn ","
  let values := fields.filterMap (fun field => field.toNat?)
  logInfo m!"parsed values: {values}"
-- ANCHOR_END: ch01_filter_map

-- ANCHOR: ch01_first_field
def firstField : List String → String
  | [] => "<empty>"
  | head :: _ => head
-- ANCHOR_END: ch01_first_field

-- ANCHOR: ch01_list_pipeline
run_cmd
  let fields := "10,oops,20".splitOn ","
  let values := fields.filterMap (fun field => field.toNat?)
  let labels := values.map (fun n => s!"n={n}")
  let total : Nat := values.foldl (fun acc n => acc + n) 0
  logInfo m!"first: {firstField fields}; labels: {labels}; total: {total}"
-- ANCHOR_END: ch01_list_pipeline

-- ANCHOR: ch01_array_tokens
run_cmd
  let tokens : Array String := #["(", "x"].push ")"
  logInfo m!"token count: {tokens.size}; middle: {tokens[1]?}"

  for piece in tokens do
    logInfo piece
-- ANCHOR_END: ch01_array_tokens

-- ANCHOR: ch01_make_message
def makeMessage : IO String := do
  let base := "hello"
  let target := "Lean"
  return s!"{base}, {target}"
-- ANCHOR_END: ch01_make_message

-- ANCHOR: ch01_greet
def greet : IO Unit := do
  let message ← makeMessage
  IO.println message
-- ANCHOR_END: ch01_greet

-- ANCHOR: ch01_theorem_endpoint
theorem add_zero_example (n : Nat) : n + 0 = n := by
  simp
-- ANCHOR_END: ch01_theorem_endpoint

-- ANCHOR: ch01_three_observations
#check (2 + 3 : Nat)
#eval (2 + 3 : Nat)

run_cmd
  let value : Nat := 2 + 3
  logInfo m!"value during command elaboration: {value}"
-- ANCHOR_END: ch01_three_observations
