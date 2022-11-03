import Lake
open Lake DSL


meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
--require aesop from git "https://github.com/JLimperg/aesop"


package ECTate {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib ECTate {
  globs := #[.andSubmodules `ECTate]

  -- add any library configuration options here
}


-- module_facet docs (mod) : FilePath := do
--   let some docGen4 ← findLeanExe? `«doc-gen4»
--     | error "no doc-gen4 executable configuration found in workspace"
--   let exeJob ← docGen4.exe.fetch
--   let modJob ← mod.leanBin.fetch
--   let buildDir := (← getWorkspace).root.buildDir
--   let docFile := mod.filePath (buildDir / "doc") "html"
--   exeJob.bindAsync fun exeFile exeTrace => do
--   modJob.bindSync fun _ modTrace => do
--     let depTrace := exeTrace.mix modTrace
--     let trace ← buildFileUnlessUpToDate docFile depTrace do
--       proc {
--         cmd := exeFile.toString
--         args := #["single", mod.name.toString]
--         env := #[("LEAN_PATH", (← getAugmentedLeanPath).toString)]
--       }
--     return (docFile, trace)

-- library_facet docs (lib) : Unit := do
--   BuildJob.mixArray (α := FilePath) <| ← lib.recBuildLocalModules #[`docs]
