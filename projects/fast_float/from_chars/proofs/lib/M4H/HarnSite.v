(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcSteps AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HarnHintTbl HarnHint.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HarnLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SB : Z := 0x7fff8000.
(* [comment removed for export] *)
Definition ldiv8 (l : lin) : option lin := ldivz l 8.
Definition shadow_of (a : lin) : option lin := match ldiv8 a with Some q => Some (laddc q SB) | None => None end.
(* [comment removed for export] *)
Definition cell (L : sst) (a : lin) : option lin := match find_cell (s_rgs L) a with Some (_, _, l) => Some l | None => None end.

(* [comment removed for export] *)
Definition cellz (L : sst) (a : lin) : option lin :=
  match cell L a with
  | Some l => Some l
  | None => match find_idx (s_rgs L) a 0 with
            | Some (i, o) => match nth_error (s_rgs L) i with
                             | Some R => match rg_kind R with
                                         | RZ => if forallb (fun j => match tget (okey (o + Z.of_nat j)) (rg_cont R) with None => true | _ => false end) (seq 0 8)
                                                 then Some (lconst 0) else None
                                         | _ => None
                                         end
                             | None => None
                             end
            | None => None
            end
  end.
(* [comment removed for export] *)
Inductive need : Type := NAt (a : lin) (n : Z) (k : rkind) | NCopy (a : lin) (sz : lin) (k : rkind) | NBase (a : lin) (k : rkind) | NNone
  | NSub (a : lin) (n : Z) (k : rkind).   (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint find_idxc (rgs : list region) (a : lin) (n : Z) (i : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match is_const (lsub a (rg_base R)), is_const (rg_size R) with
               | Some o, Some z => if (Z.leb 0 o && Z.leb (o + n) z && Z.ltb o z)%bool then Some (i, o) else find_idxc rs a n (S i)
               | _, _ => find_idxc rs a n (S i)
               end
  end.
(* [comment removed for export] *)
Fixpoint find_base (rgs : list region) (a : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: rs => if lin_eqb (rg_base R) a then Some i else find_base rs a (S i)
  end.
Definition find_view (L : sst) (nd : need) : option (vop * Z * rkind) :=
  match nd with
  | NAt a n k => match find_idxc (s_rgs L) a n 0 with
                 | Some (i, o) => match nth_error (s_rgs L) i with
                                  | Some R => if (Z.eqb o 0 && lin_eqb (rg_size R) (lconst n))%bool then Some (VCopy i, 0, k) else Some (VSub i o, n, k)
                                  | None => None
                                  end
                 | None => None
                 end
  | NCopy a sz k => match find_base (s_rgs L) a 0 with
                    | Some i => match nth_error (s_rgs L) i with
                                | Some R => if lin_eqb (rg_size R) sz then Some (VCopy i, 0, k) else None
                                | None => None
                                end
                    | None => None
                    end
  | NBase a k => match find_base (s_rgs L) a 0 with Some i => Some (VCopy i, 0, k) | None => None end
  | NNone => None
  | NSub a n k => match find_idxc (s_rgs L) a n 0 with Some (i, o) => Some (VSub i o, n, k) | None => None end
  end.
Definition all_views (L : sst) (nds : list need) : list (nat * option (vop * Z * rkind)) :=
  map_i (fun j nd => (j, find_view L nd)) 0 nds.

(* [comment removed for export] *)
Definition rgk (L : sst) (k : Z) : lin := rget (s_regs L) (rk k).
Definition oshadow (a : lin) : lin := match shadow_of a with Some l => l | None => lconst 0 end.
(* [comment removed for export] *)
Definition hidx (h : lin) (k : Z) : lin :=
  LIN (l_c h mod 2 ^ k) (List.filter (fun '(_, c) => negb (Z.eqb (c mod 2 ^ k) 0)) (l_t h)).
Definition hbase (h : lin) (k : Z) : lin :=
  LIN (l_c h - l_c h mod 2 ^ k) (List.filter (fun '(_, c) => Z.eqb (c mod 2 ^ k) 0) (l_t h)).
(* [comment removed for export] *)
Definition needs_fcx (vsz voff clo cln : Z) (L : sst) : list need :=
  let T := rgk L 10 in let TL := rgk L 11 in let V := rgk L 12 in let SP := rgk L 2 in
  match cell L (lconst 0x617f80), cell L (lconst 0x639328), cell L (lconst 0x617f88) with
  | Some FS, Some CTX, Some BLK =>
      let THR := match cell L (laddc CTX 152) with Some l => l | None => lconst 0 end in
      let h4 := match cellz L (laddc FS 32) with Some h => h | None => lvar 1 end in
      let Y4 := hidx h4 10 in
      let fs4 := match is_const Y4 with
                 | Some P4 =>
                     [NAt (laddc FS 32) 8 RW; NAt (laddc FS 0x8800) P4 RZ; NAt (laddc FS (0x8800 + P4)) 1 RZ; NAt (laddc FS (0x8801 + P4)) (1023 - P4) RZ;
                      NAt (laddc FS 0x409000) (1024 * P4) RW; NAt (laddc FS (0x409000 + 1024 * P4)) 1024 RW;
                      NAt (laddc FS (0x409400 + 1024 * P4)) (1024 * (1023 - P4)) RW;
                      NAt (oshadow (laddc FS 0x409000)) (128 * P4) RW; NAt (oshadow (laddc FS (0x409000 + 1024 * P4))) 128 RW;
                      NAt (oshadow (laddc FS (0x409400 + 1024 * P4))) (128 * (1023 - P4)) RW]
                 | None =>   (* [comment removed for export] *)
                     let slot := ladd (laddc FS 0x409000) (lscale 1024 Y4) in
                     [NAt (laddc FS 32) 8 RW; NBase (laddc FS 0x8800) RZ; NBase (ladd (laddc FS 0x8800) Y4) RZ; NBase (ladd (laddc FS 0x8801) Y4) RZ;
                      NBase (laddc FS 0x409000) RW; NBase slot RW; NBase (laddc slot 1024) RW;
                      NBase (oshadow (laddc FS 0x409000)) RW; NBase (oshadow slot) RW; NBase (oshadow (laddc slot 1024)) RW]
                 end in
      [NCopy T (lsub TL T) RT; NAt (oshadow (laddc T (-1))) 3 RZ; NAt V vsz RW; NAt (oshadow (laddc V (- voff))) 1 RZ;
       NAt (laddc SP (-4224)) 4096 RW; NAt (laddc SP (-128)) 128 RW; NAt (lconst 0x10000) 0x2e000 RO; NAt (lconst 0xe4db8) 12 RW;
       NAt (lconst (SB + 0x44fe)) 32 RZ; NAt (lconst (SB + 0x2060)) 0x30 RZ; NAt (lconst (SB + 0x4538)) 1302 RZ; NAt (lconst (SB + clo)) cln RZ;
       NAt (lconst 0xe1278) 4 RO; NAt (lconst 0xd9000) 0x5000 RO; NAt (lconst 0xde9d0) 0x188 RO] ++ fs4 ++
      (* [comment removed for export] *)
      let W5 := match is_const Y4 with Some 1023 => NSub | _ => NAt end in
      [NAt (laddc FS 40) 8 RW; W5 (laddc FS 0x8C00) 512 RZ; W5 (laddc FS 0x509000) (2 ^ 20) RW; W5 (oshadow (laddc FS 0x509000)) (2 ^ 17) RW;
       NAt (laddc FS 88) 16 RW;
       NAt (lconst 0xe4620) 8 RW; NAt (lconst 0xe5a98) 2 RW; NAt (lconst 0xe5aa0) 24 RW; NAt (lconst 0x174858) 4 RW; NAt (lconst 0x176971) 1 RW;
       NAt (lconst 0x617f28) 8 RW; NAt (lconst 0x617f78) 56 RW; NAt (lconst 0x639328) 8 RW; NAt CTX 160 RW; NAt THR 80 RW; NAt BLK 32 RW;
       NAt (oshadow (laddc SP (-4416))) 552 RZ; NAt (oshadow (laddc FS 0x309000)) 0x20000 RW;
       NAt (lconst (SB + 0x4a50)) 20 RZ; NAt (lconst (SB + 0x4a68)) 32 RZ]
  | _, _, _ => []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition isolate (S : sst) (a : lin) (n : Z) : option (list rstep) :=
  match find_idx (s_rgs S) a 0 with
  | Some (i, o) => match nth_error (s_rgs S) i with
                   | Some R => match is_const (rg_size R) with
                               | Some z => Some (cut_steps i (rg_base R) (rg_cont R) z 0 ((if Z.eqb o 0 then [] else [o]) ++ (if Z.eqb (o + n) z then [] else [o + n])))
                               | None => None
                               end
                   | None => None
                   end
  | None => None
  end.
(* [comment removed for export] *)
Definition few_t (l : lin) : bool := match l_t l with _ :: _ :: _ :: _ => false | _ => true end.
Fixpoint find_rg_few (fs : list fact) (rgs : list region) (a : lin) (w : Z) (i : nat) : option (nat * region * (Z * Z)) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_cz R with
               | Some _ => find_rg_few fs rs a w (S i)
               | None => if few_t (lsub a (rg_base R))
                         then match rg_off_sym fs R a w with Some r => Some (i, R, r) | None => find_rg_few fs rs a w (S i) end
                         else find_rg_few fs rs a w (S i)
               end
  end.
Definition find_rg_fast (fs : list fact) (rgs : list region) (a : lin) (w : Z) : option (nat * region * (Z * Z)) :=
  match find_rg_c (irange fs a) w rgs O with
  | Some r => Some r
  | None => match find_rg_few fs rgs a w O with Some r => Some r | None => find_rg_sym fs rgs a w O end
  end.
(* [comment removed for export] *)
Definition split_at (S : sst) (p m : lin) : option (nat * lin * lin) :=
  match find_idx (s_rgs S) p 0 with
  | Some (i, _) => Some (i, p, m)
  | None => match is_const m with
            | Some mz => match find_rg_fast (s_facts S) (s_rgs S) p mz with Some (i, _, _) => Some (i, p, m) | None => None end
            | None => None
            end
  end.
(* [comment removed for export] *)
Definition retype_at (S : sst) (p : lin) (k : rkind) : option (nat * rkind) :=
  match find_base (s_rgs S) p 0 with Some i => Some (i, k) | None => None end.
(* [comment removed for export] *)
Definition merge_at (S : sst) (p : lin) (n : nat) : option (nat * nat) :=
  match find_base (s_rgs S) p 0 with Some i => Some (i, n) | None => None end.
(* [comment removed for export] *)
Definition mergecc_at (S : sst) (p : lin) : option (list rstep) :=
  match find_base (s_rgs S) p 0 with Some i => Some [RMergeCC i] | None => None end.

(* [comment removed for export] *)
Definition cs_isolate (S : sst) : option (list rstep) := isolate S (rgk S 10) 23.
Definition cs_split_text (S : sst) : option (nat * lin * lin) := split_at S (rgk S 10) (lsub (rgk S 11) (rgk S 10)).
Definition cs_rt_text (S : sst) : option (nat * rkind) := retype_at S (rgk S 10) RT.
(* [comment removed for export] *)
Definition cs_split_ssh (S : sst) : option (nat * lin * lin) := split_at S (oshadow (laddc (rgk S 2) (-4416))) (lconst 560).
(* [comment removed for export] *)
Definition cs_unz_ssh (S : sst) : option nat :=
  match find_rg_fast (s_facts S) (s_rgs S) (oshadow (laddc (rgk S 2) (-4416))) 560 with Some (i, _, _) => Some i | None => None end.
Definition needs_fcv (vsz : Z) : sst -> list need := if Z.eqb vsz 8 then needs_fcx 8 0 0x4a89 0x2e else needs_fcx 4 4 0x4ab8 0x12.
Definition needs_fc := needs_fcv 8.
(* [comment removed for export] *)
Definition needs_fci (L : sst) : list need :=
  let T := rgk L 10 in let TL := rgk L 11 in let V := rgk L 12 in let SP := rgk L 2 in
  [NCopy T (lsub TL T) RT; NAt (oshadow (laddc T (-1))) 3 RZ; NAt V 4 RW; NAt (oshadow V) 1 RZ; NAt (laddc SP (-128)) 128 RW;
   NAt (lconst 0xdcc10) 8 RO; NAt (lconst 0xe4db8) 8 RW; NAt (lconst 0x227f0) 256 RO; NAt (lconst (SB + 0x44fe)) 32 RZ;
   NAt (lconst 0x103a8) 16 RO; NAt (lconst 0x103f8) 16 RO; NAt (lconst 0x10470) 16 RO; NAt (lconst (SB + 0x2075)) 0x1a RZ;
   NAt (lconst 0x25650) 0x330 RO; NAt (lconst 0x7fffcaca) 0x66 RZ].
Definition specs_of (nds : sst -> list need) (S : sst) : list (vop * Z * rkind) :=
  List.map (fun '(_, v) => match v with Some x => x | None => (VCopy 0, 0, RW) end) (all_views S (nds S)).
Definition cs_specs := specs_of needs_fc.
Definition cs_specs_f := specs_of (needs_fcv 4).
Definition cs_specs_i := specs_of needs_fci.

(* [comment removed for export] *)
Definition hkey_site (P0 S : sst) : list Z := [2; s_pc S; Zpos (s_next S); Z.of_nat (List.length (s_facts S)); Z.of_nat (List.length (s_facts P0)); s_pc P0].
Definition cs_want (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (S : sst) : list fact :=
  let Lw := with_rgs S (views_of (specs S) S) in
  let σc := mcall Lw P0 in
  let cands := List.map (fsubst σc) (s_facts P0) in
  let run := fun (m : hmode) (st : hst) => filter_h (fun st f => let '(b, st') := ask_b m st (fun _ => fact_implied (s_facts S) f) in (negb b, st')) cands st in
  if HINT_REC then let '(w, st) := run HRec hst0 in w ++ [hmarker (hkey_site P0 S) st]
  else if HINT_STRICT then
    match hint_lookup (hkey_site P0 S) with
    | Some (bits, hull) => let '(w, st) := run HReplay (hst_replay bits hull) in if hst_done st then w else []      (* [comment removed for export] *)
    | None => []                                                                                               (* [comment removed for export] *)
    end
  else fst (run HReal hst0).

(* [comment removed for export] *)
Definition at_c (S : sst) (a : lin) (n : nat) : option (nat * Z * nat) :=
  match find_idxc (s_rgs S) a (Z.of_nat n) 0 with Some (i, o) => Some (i, o, n) | None => None end.
Definition at1 (S : sst) (a : lin) : option (nat * Z) :=
  match find_idxc (s_rgs S) a 1 0 with Some (i, o) => Some (i, o) | None => None end.
Definition FSof (S : sst) : lin := match cell S (lconst 0x617f80) with Some l => l | None => lconst 0 end.
Definition BLKof (S : sst) : lin := match cell S (lconst 0x617f88) with Some l => l | None => lconst 0 end.
Definition THRof (S : sst) : lin :=
  match cell S (lconst 0x639328) with Some c => match cell S (laddc c 152) with Some l => l | None => lconst 0 end | None => lconst 0 end.
Definition cs_zrt_h4 (S : sst) := at_c S (laddc (FSof S) 32) 8.
Definition cs_zrt_h5 (S : sst) := at_c S (laddc (FSof S) 40) 8.
Definition cs_zbk_fsh (S : sst) := at_c S (laddc (FSof S) 89) 8.
Definition cs_zbk_tsd (S : sst) := at_c S (lconst 0xe4621) 7.
Definition cs_zbk_hme (S : sst) := at_c S (lconst 0xe5aa8) 16.
(* [comment removed for export] *)
Definition cs_zbk_lsan (S : sst) := at_c S (lconst 0x617f90) 4.
Definition cs_zbk_tsd0 (S : sst) := at_c S (lconst 0xe461c) 4.
Definition cs_rb1_fb (S : sst) := at1 S (lconst 0x176971).
Definition cs_rbk_tlsb (S : sst) := at_c S (laddc (THRof S) 48) 8.
Definition cs_rbk_tlse (S : sst) := at_c S (laddc (THRof S) 56) 8.
Definition cs_rbk_beg (S : sst) := at_c S (laddc (BLKof S) 24) 8.
(* [comment removed for export] *)
Definition cs_scl_fs8 (S : sst) : option (lin * Z) := match ldivz (FSof S) 8 with Some l => Some (l, 3) | None => None end.
Definition cs_scl_fsp (S : sst) : option (lin * Z) := match ldivz (FSof S) 4096 with Some l => Some (l, 12) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tb_sso (r : Z) (S : sst) : lin := laddc (rgk S r) 1.
Definition cs_rw_text (tb : sst -> lin) (S : sst) : option (nat * rkind) := retype_at S (tb S) RW.
Definition cs_mrg_text (tb : sst -> lin) (S : sst) : option (nat * nat) := merge_at S (tb S) 2.
Definition cs_mcc_text (tb : sst -> lin) (S : sst) : option (list rstep) :=
  match find_base (s_rgs S) (tb S) 0 with Some i => match i with O => None | Datatypes.S i' => Some [RMergeCC i; RMergeCC i'] end | None => None end.
(* [comment removed for export] *)
Definition cs_mrg_ssh (S : sst) : option (nat * nat) :=
  match find_base (s_rgs S) (oshadow (laddc (rgk S 2) (-4416))) 0 with
  | Some i => match i with O => None | Datatypes.S i' => Some (i', 3%nat) end
  | None => match find_rg_fast (s_facts S) (s_rgs S) (oshadow (laddc (rgk S 2) (-4416))) 560 with
            | Some (i, _, _) => match i with O => None | Datatypes.S i' => Some (i', 3%nat) end
            | None => None
            end
  end.
