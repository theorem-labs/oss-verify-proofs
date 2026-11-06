(* Theorem Labs, 2026-10-29: B patch 08 - this per-image copy of YCbq is retired; every B file Requires
   lib.Reusable.YCbq, so identity has ONE ajournal. Sound because identity's A and B images have the same
   range (0x10000 .. 0x5fa000, derived from each pin's PT_LOADs). Do not copy to a unit whose images differ. *)
