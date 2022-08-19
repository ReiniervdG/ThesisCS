import Lake
open Lake DSL

package struct {
  -- add package configuration options here
}

lean_lib Struct {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe struct {
  root := `Struct
}
