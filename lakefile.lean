import Lake
open Lake DSL

package «Fun» where
  -- add package configuration options here

lean_lib «Fun» where
  -- add library configuration options here

@[default_target]
lean_exe «fun» where
  root := `Main
