(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.

Module M4B_tmpl.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
Local Open Scope Z_scope.

Fixpoint regs_pat (k : nat) (acc : tree lin) : tree lin :=
  match k with O => acc | S k' => regs_pat k' (tset (Pos.of_succ_nat k) (lvar (100 + Pos.of_nat k)) acc) end.
Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Fixpoint rsets (R : tree lin) (l : list (Z * lin)) : tree lin :=
  match l with [] => R | (k, v) :: l' => rsets (rset R (rk k) v) l' end.
Fixpoint mk_imgs_acc (rs : list (Z * nat)) (t : tree Z) : tree Z :=
  match rs with [] => t | (lo, n) :: r => mk_imgs_acc r (mk_img_acc BSEGS n (Z.shiftr lo 3) t) end.
Lemma mk_imgs_acc_ok : forall rs t, Forall (fun r => 0 <= fst r) rs -> img_ok BSEGS t -> img_ok BSEGS (mk_imgs_acc rs t).
Proof.
  intros rs. induction rs as [|[lo n] rs IH]; intros t Hf Ht; cbn [mk_imgs_acc]; [exact Ht|].
  apply Forall_cons_iff in Hf as [Hx Hf']. cbn [fst] in Hx. apply IH; [exact Hf'|].
  apply mk_img_acc_ok; [apply Z.shiftr_nonneg; lia | exact Ht].
Qed.
(* [comment removed for export] *)
Definition bk8 (z : Z) : list bval := List.map (fun j => BK (Z.land (Z.shiftr z (8 * Z.of_nat j)) 255)) (seq 0 8).
Definition bkn (n : nat) (z : Z) : list bval := List.map (fun j => BK (Z.land (Z.shiftr z (8 * Z.of_nat j)) 255)) (seq 0 n).
Definition bv8 (l : lin) : list bval := List.map (fun j => BV l (Z.of_nat j)) (seq 0 8).

Definition SHB : Z := 0x7fff8000.
Definition KHI : Z := 0x10007fff8000.
Definition KTOP : Z := 2 ^ 47.
Definition TPV : Z := 0x619840.

(* [comment removed for export] *)
Definition T := lvar 1. Definition L := lvar 2. Definition XV := lvar 3. Definition SP := lvar 4. Definition RA := lvar 5.
Definition FMT := lvar 6. Definition Y0 := lvar 7. Definition Y1 := lvar 8.
Definition FSP := lvar 10. Definition H4 := lvar 11. Definition P4 := lvar 12. Definition H5 := lvar 13. Definition P5 := lvar 14.
Definition CTX := lvar 15. Definition THR := lvar 16. Definition BLK := lvar 17. Definition BEG := lvar 18.
Definition TLSB := lvar 19. Definition TLSE := lvar 20. Definition FB := lvar 21.
Definition TL := ladd T L.
(* [comment removed for export] *)
Definition V := XV. Definition VS := lvar 29.
Definition v_facts : list fact :=
  [FRange V KHI (KTOP - 8); FMod V 3 0; FRange (lsub (lscale 8 (lsub VS (lconst SHB))) V) 0 0; FRange VS (SHB + KHI / 8) (SHB + KTOP / 8)].
Definition FS := lscale 4096 FSP.
(* [comment removed for export] *)
Definition fsc (c : Z) : lin := laddc FS c.
Definition fsh (c : Z) : lin := laddc (lscale 512 FSP) (SHB + c / 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FL4 : Z := 0x8800. Definition FL5 : Z := 0x8C00.
Definition AR4 : Z := 0x409000. Definition AR5 : Z := 0x509000.
(* [comment removed for export] *)
Definition fks4_split : list region :=
  [ track (RGz (fsc 32) 8 RW TEmpty) 0 (bv8 H4);                                   (* [comment removed for export] *)
    RG (fsc FL4) P4 RZ TEmpty;                                                    (* [comment removed for export] *)
    RG (ladd (fsc FL4) P4) (lconst 1) RZ TEmpty;                                  (* [comment removed for export] *)
    RG (ladd (fsc (FL4 + 1)) P4) (laddc (lscale (-1) P4) 1023) RZ TEmpty;         (* [comment removed for export] *)
    RG (fsc AR4) (lscale 1024 P4) RW TEmpty;                                      (* [comment removed for export] *)
    RG (ladd (fsc AR4) (lscale 1024 P4)) (lconst 1024) RW TEmpty;                 (* [comment removed for export] *)
    RG (ladd (fsc (AR4 + 1024)) (lscale 1024 P4)) (laddc (lscale (-1024) P4) (1024 * 1023)) RW TEmpty;
    RG (fsh AR4) (lscale 128 P4) RW TEmpty;                                       (* [comment removed for export] *)
    RG (ladd (fsh AR4) (lscale 128 P4)) (lconst 128) RW TEmpty;
    RG (ladd (fsh (AR4 + 1024)) (lscale 128 P4)) (laddc (lscale (-128) P4) (128 * 1023)) RW TEmpty ].
Definition fks4_facts : list fact := [FRange P4 0 1023; FMod (lsub H4 P4) 10 0].
(* [comment removed for export] *)
Definition fks5_whole : list region :=
  [ track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 H5);
    RGz (fsc FL5) 512 RZ TEmpty;
    RGz (fsc AR5) (2 ^ 20) RW TEmpty;
    RGz (fsh AR5) (2 ^ 17) RW TEmpty ].
(* [comment removed for export] *)
Definition fs_hdr : region := track (RGz (fsc 88) 16 RW TEmpty) 0 (bk8 20 ++ [BK 0]).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPV := lvar 60. Definition SBOTV := lvar 61.
Definition rt_tp0 : region := track (track (track (track (RGz (lconst 0x619838) 56 RW TEmpty) 0 (bk8 0x619860)) 8 (bv8 FS)) 16 (bv8 BLK)) 48 (bk8 0x61a040).
Definition rt_tp : region := track rt_tp0 24 (bkn 4 0).
Definition rt_rgs : list region :=
  [ track (RGz (lconst 0xe5ee0) 8 RW TEmpty) 0 (bkn 8 1);                          (* [comment removed for export] *)
    track (RGz (lconst 0xe7358) 2 RW TEmpty) 0 [BK 1; BK 1];                        (* [comment removed for export] *)
    track (RGz (lconst 0xe7360) 24 RW TEmpty) 0 (bk8 (KTOP - 1) ++ bk8 0 ++ bk8 0); (* [comment removed for export] *)
    track (RGz (lconst 0x176118) 4 RW TEmpty) 0 (bkn 4 0);                          (* [comment removed for export] *)
    track (RGz (lconst 0x178231) 1 RW TEmpty) 0 [BV FB 0];                          (* [comment removed for export] *)
    track (RGz (lconst 0x6197e8) 8 RW TEmpty) 0 (bk8 0x63abe8);                     (* [comment removed for export] *)
    rt_tp;                                                                          (* [comment removed for export] *)
    track (RGz (lconst 0x63abe8) 8 RW TEmpty) 0 (bv8 CTX);                          (* [comment removed for export] *)
    track (track (RGz CTX 160 RW TEmpty) 8 (bkn 4 0)) 152 (bv8 THR);                   (* [comment removed for export] *)
    track (track (track (track (track (RGz THR 80 RW TEmpty) 0 (bv8 CTX)) 8 (bv8 STOPV)) 16 (bv8 SBOTV)) 40 [BK 0]) 48 (bv8 TLSB ++ bv8 TLSE);
    track (RGz BLK 32 RW TEmpty) 24 (bv8 BEG) ].
(* [comment removed for export] *)
Definition relro_rgs : list region := [ RGz (lconst 0xda000) 0x6000 RO TEmpty; RGz (lconst 0xe0250) 0x188 RO TEmpty ].
(* [comment removed for export] *)
Definition SH_LO : Z := 0x7fff7000.
Definition IMG_END : Z := 0x63c000.
Definition two_class (X : lin) (n : Z) : list fact :=
  [FRange X IMG_END (KTOP - n); FRange (lsub X (lconst KHI)) 0 (2 ^ 64 + SH_LO - n - KHI)].
(* [comment removed for export] *)
Definition two_class4k (X : lin) (n : Z) : list fact :=
  [FRange X 4096 (KTOP - n); FRange (lsub X (lconst KHI)) 0 (2 ^ 64 + SH_LO - n - KHI)].
Definition rt_facts : list fact :=
  [ FRange FSP (IMG_END / 4096) ((KTOP - 0xb09000) / 4096); FRange (lsub FS (lconst KHI)) 0 (2 ^ 64 + SH_LO - 0xb09000 - KHI) ]
  ++ two_class CTX 160 ++ two_class4k THR 80 ++ two_class4k BLK 32 ++
  [ FRange BEG 1 (2 ^ 64 - 1); FRange FB 1 255; FMod CTX 3 0; FMod THR 3 0; FMod BLK 3 0;
    (* [comment removed for export] *)
    FRange (lsub CTX FS) 0xb09000 (2 ^ 64 - 160); FRange (lsub THR FS) 0xb09000 (2 ^ 64 - 80); FRange (lsub BLK FS) 0xb09000 (2 ^ 64 - 32) ].
(* [comment removed for export] *)
Definition SPSH := lvar 9.
Definition spsh_fact (lo : Z) : fact := FRange (lsub (lscale 8 (lsub SPSH (lconst SHB))) (laddc SP (- lo))) 0 0.
Definition fk3sh : region := RGz (fsh 0x309000) 0x20000 RW TEmpty.
Definition tbl10sh : region := RGz (lconst (SHB + 0x4a54)) 20 RZ TEmpty.
Definition pow5tabsh : region := RGz (lconst (SHB + 0x4a6c)) 32 RZ TEmpty.
(* [comment removed for export] *)
Definition sb_uar : region := track (RGz (lconst 0xe6678) 12 RW TEmpty) 0 (bk8 SHB ++ bkn 4 1).

(* [comment removed for export] *)
Definition KEEPR : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Fixpoint regs_keep (R : tree lin) (k : nat) (nx : positive) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => regs_keep R k' nx (tset (Pos.of_succ_nat k)
                                    (if existsb (Z.eqb (Z.of_nat k)) KEEPR then rget R (Pos.of_succ_nat k) else lvar (nx + Pos.of_nat k)) acc)
  end.
Definition set_rg_cont (rgs : list region) (i : nat) (c : tree bval) : list region :=
  map_i (fun j R => if Nat.eqb j i then RG (rg_base R) (rg_size R) (rg_kind R) c else R) 0 rgs.
Definition put_bvs (c : tree bval) (o : Z) (bvs : list bval) : tree bval := put_bytes c o bvs.
Definition hint_lin (R : region) : lin := match tget (okey 0) (rg_cont R) with Some (BV l 0) => l | _ => lconst 0 end.
Definition smalloc_cont (ia ih ifl isl ish : nat) (SZ : Z) (slot flb : lin) (L : sst) : option sst :=
  match is_const (rget (s_regs L) (rk 1)) with
  | None => None
  | Some ret =>
      let nx := s_next L in
      let R := rset (regs_keep (s_regs L) 31 nx TEmpty) (rk 10) slot in
      let rh := nth ih (s_rgs L) (RGz (lconst 0) 0 RW TEmpty) in
      let rg1 := set_rg_cont (s_rgs L) ia TEmpty in
      let rg2 := set_rg_cont rg1 ih (put_bvs TEmpty 0 (bv8 (laddc (hint_lin rh) 1))) in
      let rg3 := set_rg_cont rg2 ifl (put_bvs TEmpty 0 [BK 1]) in
      let rg4 := set_rg_cont rg3 isl (put_bvs (put_bvs TEmpty 24 (bv8 (rget (s_regs L) (rk 2)))) (SZ - 8) (bv8 flb)) in
      let rg5 := set_rg_cont rg4 ish (put_bvs TEmpty 0 (List.repeat (BK 0) (Z.to_nat (SZ / 8)))) in
      Some (SST ret R rg5 (s_facts L) (nx + 32) RNone)
  end.
Definition SLOT4 : lin := ladd (fsc AR4) (lscale 1024 P4).
Definition FLB4 : lin := ladd (fsc FL4) P4.
(* [comment removed for export] *)
End M4B_tmpl.

Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl.
Import ListNotations.

Module M4B_fci.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
Local Open Scope Z_scope.

Fixpoint regs_pat (k : nat) (acc : tree lin) : tree lin :=
  match k with O => acc | S k' => regs_pat k' (tset (Pos.of_succ_nat k) (lvar (100 + Pos.of_nat k)) acc) end.
Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Fixpoint rsets (R : tree lin) (l : list (Z * lin)) : tree lin :=
  match l with [] => R | (k, v) :: l' => rsets (rset R (rk k) v) l' end.
Fixpoint mk_imgs_acc (rs : list (Z * nat)) (t : tree Z) : tree Z :=
  match rs with [] => t | (lo, n) :: r => mk_imgs_acc r (mk_img_acc BSEGS n (Z.shiftr lo 3) t) end.

Definition TM : tree xi := Eval vm_compute in mk_tbl BSEGS 0x9d970 419.
Definition IMGW : tree Z := Eval vm_compute in mk_imgs_acc [(0xde490, 1%nat); (0x22800, 33%nat); (0x103a8, 2%nat); (0x103f8, 2%nat); (0x10470, 2%nat); (0x25670, 0x66%nat)] TEmpty.
Definition B : Z := 2 ^ 46.
Definition SHB : Z := 0x7fff8000.
(* [comment removed for export] *)
Definition T := lvar 1. Definition L := lvar 2. Definition XV := lvar 3. Definition SP := lvar 4. Definition RA := lvar 5.
Definition Y0 := lvar 7. Definition Y1 := lvar 8.
Definition TL := ladd T L. Definition V := XV. Definition VS := lvar 29.
Definition R0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, T); (11, TL); (12, V); (13, lconst 5); (14, lconst 42949673006); (1, RA); (2, SP)].
Definition F0 : list fact := [FRange (lsub T (lscale 8 Y0)) 0 16; FRange (lsub (lscale 8 Y1) T) 1 256; FRange (lsub (lscale 8 Y1) TL) 1 256;
   FRange (lsub Y1 Y0) 1 32; FRange L 0 128; FRange T 6537216 140737488355072; FRange Y0 800288 17592186044416; FRange Y1 800288 17592186044416;
   FRange V 17592186011648 140737488355320; FMod V 3 0; FRange (lsub (lscale 8 (lsub VS (lconst SHB))) V) 0 0; FRange VS 2201170702336 17594333495296; FRange SP 17592186011904 140737488355328; FMod SP 4 0].
Definition bk8 (z : Z) : list bval := List.map (fun j => BK (Z.land (Z.shiftr z (8 * Z.of_nat j)) 255)) (seq 0 8).
Definition RGS : list region :=
  [ RG T L RT TEmpty;                                    (* [comment removed for export] *)
    RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty;    (* [comment removed for export] *)
    RGz V 4 RW TEmpty;                                   (* [comment removed for export] *)
    RGz VS 1 RZ TEmpty;                                  (* [comment removed for export] *)
    RGz (laddc SP (-128)) 128 RW TEmpty;                 (* [comment removed for export] *)
    RGz (lconst 0xde490) 8 RO TEmpty;                    (* [comment removed for export] *)
    track (RGz (lconst 0xe6678) 8 RW TEmpty) 0 (bk8 SHB); (* [comment removed for export] *)
    RGz (lconst 0x22800) 256 RO TEmpty;                  (* [comment removed for export] *)
    RGz (lconst (0x7fff8000 + 0x4500)) 32 RZ TEmpty;     (* [comment removed for export] *)
    RGz (lconst 0x103a8) 16 RO TEmpty; RGz (lconst 0x103f8) 16 RO TEmpty; RGz (lconst 0x10470) 16 RO TEmpty;  (* [comment removed for export] *)
    RGz (lconst (0x7fff8000 + 0x2075)) 0x1a RZ TEmpty;   (* [comment removed for export] *)
    RGz (lconst 0x25670) 0x330 RO TEmpty;                (* [comment removed for export] *)
    RGz (lconst 0x7fffcace) 0x66 RZ TEmpty ].            (* [comment removed for export] *)
Definition P0 : sst := SST 0x9d970 R0 RGS F0 200 RNone.


(* [comment removed for export] *)
Definition STOPS : list Z := [0x9d9d8; 0x9dabc; 0x9db78; 0x9dd8c].
Definition LV := Eval vm_compute in fx_explore TM IMGW 2000 STOPS P0 [].
Definition LZs := Eval vm_compute in List.filter (fun s => Z.eqb (s_pc s) 0x9dabc) LV.
Definition regdiff (A B : sst) : list (Z * lin * lin) :=
  List.flat_map (fun k => let a := rget (s_regs A) (rk k) in let b := rget (s_regs B) (rk k) in if lin_eqb a b then [] else [(k, a, b)]) (List.map Z.of_nat (seq 1 31)).
Definition LZ0 := Eval vm_compute in nth 0 LZs P0.
Definition P := lvar 300. Definition SV := lvar 302.
Definition LSZ_PL : sst := Eval vm_compute in
  SST 0x9dabc (rsets (s_regs LZ0) [(13, P); (15, P); (29, SV); (28, lvar 301)]) (s_rgs LZ0)
      (FRange (lsub TL P) 1 128 :: FRange (lsub P T) 0 (2 ^ 40) :: FRange (lsub SV T) 0 1 :: F0) 310 RNone.
Definition LSZ : loopspec := LS LSZ_PL (lsub TL P) (map Pos.of_nat (seq 1 299)) 400 [0x9db78; 0x9dd8c].
Definition PLAN2 : plan := PRun 2000 STOPS [(0x9dabc, PLoop LSZ [])].
Definition D2a := Eval vm_compute in check TM IMGW (vars_below (s_next P0)) 10 PLAN2 P0.
Definition LW0 := Eval vm_compute in match D2a with Some l => nth 0 (List.filter (fun s => Z.eqb (s_pc s) 0x9db78) l) P0 | None => P0 end.
Definition G := lvar 303. Definition R0v := lvar 304.
Definition PW := ladd (lscale 8 G) R0v.
Definition LSW_PL : sst := Eval vm_compute in
  SST 0x9db78 (rsets (s_regs LW0) [(18, ladd G (lconst SHB)); (16, PW); (17, PW); (31, lsub TL PW); (28, lvar 305); (13, lvar 306); (27, lvar 307);
                                    (1, lvar 308); (7, lvar 309); (12, lvar 311); (5, lvar 312); (15, P)]) (s_rgs LW0)
      (FRange R0v 0 7 :: FRange (lsub TL PW) 8 128 :: FRange (lsub PW T) 0 (2 ^ 40) :: FRange (lsub G Y0) 0 32 :: FRange (lsub Y1 G) 2 32 ::
       FRange (lsub P T) 0 (2 ^ 40) :: FRange (lsub TL P) 0 128 :: F0) 320 RNone.
Definition LSW : loopspec := LS LSW_PL (lsub TL PW) (map Pos.of_nat (seq 1 299)) 400 [0x9dc98; 0x9dc80].
Definition PLAN3 : plan := PRun 2000 STOPS [(0x9dabc, PLoop LSZ [(0x9db78, PLoop LSW [])]); (0x9db78, PLoop LSW [])].
Definition D3 := Eval vm_compute in check TM IMGW (vars_below (s_next P0)) 10 PLAN3 P0.
Definition KRUN : plan := PRun 1000 [0x9dd8c] [].
Definition NODES1 : list (Z * waction) :=
  [ (0x9dabc, WTmpl LSZ_PL (PLoop LSZ []));
    (0x9db78, WTmpl LSW_PL (PLoop LSW []));
    (0x9dc98, WPlan KRUN); (0x9dc80, WPlan KRUN) ].
Definition P0RUN : plan := PRun 2000 STOPS [].
Definition LC0 := Eval vm_compute in
  match check TM IMGW (vars_below (s_next P0)) 10 P0RUN P0 with
  | Some f => match wcheck TM IMGW (vars_below (s_next P0)) 10 P0 NODES1 f with
              | Some l => nth 0 (List.filter (fun s => Z.eqb (s_pc s) 0x9dd8c) l) P0
              | None => P0
              end
  | None => P0
  end.
Definition P2 := lvar 330.
Definition LSC_PL : sst := Eval vm_compute in
  SST 0x9dd8c (rsets (s_regs LC0) [(13, P2); (16, P2); (28, lvar 331); (17, lvar 332); (12, lvar 333); (18, lvar 334); (7, lvar 335);
                                     (1, lvar 336); (5, lvar 337); (22, lvar 338); (23, lvar 339); (24, lvar 340); (25, lvar 341);
                                     (26, lvar 342); (27, lvar 343)]) (s_rgs LC0)
      (FRange (lsub TL P2) 1 128 :: FRange (lsub P2 T) 0 (2 ^ 40) :: FRange (lsub P T) 0 (2 ^ 40) :: FRange (lsub TL P) 0 128 :: F0) 350 RNone.
Definition LSC : loopspec := LS LSC_PL (lsub TL P2) (map Pos.of_nat (seq 1 299)) 400 [0x9df14; 0x9ddf4].
Definition NODES : list (Z * waction) :=
  NODES1 ++
  [ (0x9dd8c, WTmpl LSC_PL (PLoop LSC []));
    (0x9df14, WPlan (PRun 1000 [] [])); (0x9ddf4, WPlan (PRun 1000 [] [])) ].

(* [comment removed for export] *)
Definition KEEPR : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Fixpoint qregs (R : tree lin) (k : nat) (nx : positive) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' => qregs R k' nx (tset (Pos.of_succ_nat k)
                                (if existsb (Z.eqb (Z.of_nat k)) KEEPR then rget R (Pos.of_succ_nat k) else lvar (nx + Pos.of_nat k)) acc)
  end.
Definition drop_cont (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) TEmpty.
(* [comment removed for export] *)
Definition Q : sst := SST 0 (qregs R0 31 200 TEmpty) (map_i (fun i R => if Nat.eqb i 6 then R else drop_cont R) 0 RGS) F0 240 RNone.
Definition RETS : list Z := [0x9df80].

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Ltac2".
Lemma FCI_cert : all_fin (fin_q Q RETS (s_next P0)) (wstart TM IMGW (vars_below (s_next P0)) 10 P0 P0RUN NODES) = true.
Proof. cert_refl_vm constr:(true). Qed.
Set Default Proof Mode "Classic".

Lemma TM_eq : TM = mk_tbl BSEGS 0x9d970 419.
Proof. vm_compute. reflexivity. Qed.
Lemma mk_imgs_acc_ok : forall rs t, Forall (fun r => 0 <= fst r) rs -> img_ok BSEGS t -> img_ok BSEGS (mk_imgs_acc rs t).
Proof.
  intros rs. induction rs as [|[lo n] rs IH]; intros t Hf Ht; cbn [mk_imgs_acc]; [exact Ht|].
  apply Forall_cons_iff in Hf as [Hx Hf']. cbn [fst] in Hx. apply IH; [exact Hf'|].
  apply mk_img_acc_ok; [apply Z.shiftr_nonneg; lia | exact Ht].
Qed.
Lemma IMGW_ok : img_ok BSEGS IMGW.
Proof.
  change (img_ok BSEGS (mk_imgs_acc [(0xde490, 1%nat); (0x22800, 33%nat); (0x103a8, 2%nat); (0x103f8, 2%nat); (0x10470, 2%nat); (0x25670, 0x66%nat)] TEmpty)).
  apply mk_imgs_acc_ok; [repeat constructor; cbn; lia|]. intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
Lemma RETS_ok : Forall (is_ret BSEGS) RETS.
Proof. unfold RETS. repeat constructor. exists (Z_to_bv 32 0x00008067). (split; [|split]); vm_refl_bv. Qed.

Theorem fci_ok : fn_ok BSEGS P0 Q RETS.
Proof.
  apply (fn_ok_of_wcert BSEGS TM IMGW 10 P0RUN NODES P0 Q RETS ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok FCI_cert).
  - intros P0' Q' H. cbn in H. destruct H.
  - intros fh H. cbn in H. destruct H.
  - intros P0' Q' H. cbn in H. destruct H.
  - intros P0' Q' pcQ H. cbn in H. destruct H.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact RETS_ok.
Qed.
End M4B_fci.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SWB := lvar 23. Definition SWS := lvar 24.
(* [comment removed for export] *)
Definition stack_facts (need : Z) : list fact :=
  [ FRange (laddc SP (- need)) KHI (KTOP - need); FMod SP 4 0; FRange (lsub SP SWB) need (2 ^ 30); FRange (lsub (ladd SWB SWS) SP) 0 (2 ^ 30);
    FRange (lsub (laddc SP (- need)) (laddc FS 0xb09000)) 0 (2 ^ 47) ].

(* [comment removed for export] *)
Definition SM4_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV)].
Definition SM4_RGS : list region :=
  [ RG SWB SWS RW TEmpty;                                              (* [comment removed for export] *)
    track (RGz (fsc 32) 8 RW TEmpty) 0 (bv8 H4);                       (* [comment removed for export] *)
    RG (fsc FL4) P4 RZ TEmpty;                                         (* [comment removed for export] *)
    RG (ladd (fsc FL4) P4) (lconst 1) RZ TEmpty;                       (* [comment removed for export] *)
    RG (ladd (fsc (FL4 + 1)) P4) (laddc (lscale (-1) P4) 1023) RZ TEmpty;  (* [comment removed for export] *)
    RG (ladd (fsc AR4) (lscale 1024 P4)) (lconst 1024) RW TEmpty;      (* [comment removed for export] *)
    RG (ladd (fsh AR4) (lscale 128 P4)) (lconst 128) RW TEmpty;        (* [comment removed for export] *)
    fs_hdr; sb_uar ] ++ rt_rgs ++ relro_rgs.
Definition SM4_F : list fact := FMod RA 1 0 :: fks4_facts ++ rt_facts ++ stack_facts 208.
Definition SM4_P0 : sst := SST 0x4b204 SM4_R0 SM4_RGS SM4_F 200 RNone.
(* [comment removed for export] *)
Definition SM4_Q : sst :=
  SST 0 (rset (regs_keep SM4_R0 31 200 TEmpty) (rk 10) SLOT4)
    ([ RG SWB SWS RW TEmpty;
       track (RGz (fsc 32) 8 RW TEmpty) 0 (bv8 (laddc H4 1));
       RG (fsc FL4) P4 RZ TEmpty;
       track (RG (ladd (fsc FL4) P4) (lconst 1) RZ TEmpty) 0 [BK 1];
       RG (ladd (fsc (FL4 + 1)) P4) (laddc (lscale (-1) P4) 1023) RZ TEmpty;
       track (track (RG (ladd (fsc AR4) (lscale 1024 P4)) (lconst 1024) RW TEmpty) 24 (bv8 SP)) 1016 (bv8 FLB4);
       track (RG (ladd (fsh AR4) (lscale 128 P4)) (lconst 128) RW TEmpty) 0 (List.repeat (BK 0) 128);
       fs_hdr; sb_uar ] ++ rt_rgs ++ relro_rgs)
    SM4_F 240 RNone.
(* [comment removed for export] *)
Definition KEEPK : list positive := List.map rk KEEPR.
Definition SM4_QK : list positive := [rk 10].

Lemma SM4_wf : state_wf SM4_P0 = true /\ state_wf SM4_Q = true /\ shape_eqb (s_rgs SM4_P0) (s_rgs SM4_Q) = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition SHSLOT4 : lin := ladd (fsh AR4) (lscale 128 P4).
(* [comment removed for export] *)
Definition SSF5_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, SHSLOT4); (11, lconst 128)].
Definition SSF5_RGS (post : bool) : list region :=
  [ RG SWB SWS RW TEmpty;                                                                 (* [comment removed for export] *)
    if post then track (RG SHSLOT4 (lconst 128) RW TEmpty) 0 (List.repeat (BK 245) 128)
            else RG SHSLOT4 (lconst 128) RW TEmpty ] ++ relro_rgs.                        (* [comment removed for export] *)
Definition SSF5_F : list fact := FMod RA 1 0 :: FRange P4 0 1023 :: rt_facts ++ stack_facts 64.
Definition SSF5_P0 : sst := SST 0x63e20 SSF5_R0 (SSF5_RGS false) SSF5_F 200 RNone.
Definition SSF5_Q : sst := SST 0 (regs_keep SSF5_R0 31 200 TEmpty) (SSF5_RGS true) SSF5_F 240 RNone.
Lemma SSF5_wf : state_wf SSF5_P0 = true /\ state_wf SSF5_Q = true /\ shape_eqb (s_rgs SSF5_P0) (s_rgs SSF5_Q) = true.
Proof. vm_compute. repeat split. Qed.


(* [comment removed for export] *)
Definition msb_R0 (o n : Z) : tree lin :=
  rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, laddc SP o); (11, lconst 0); (12, lconst n)].
Definition msb_RGS (post : bool) (o n : Z) : list region :=
  [ RG SWB SWS RW TEmpty;                                                       (* [comment removed for export] *)
    (if post then track (RG (laddc SP o) (lconst n) RW TEmpty) 0 (List.repeat (BK 0) (Z.to_nat n))
     else RG (laddc SP o) (lconst n) RW TEmpty);                                (* [comment removed for export] *)
    RGz SPSH 40 RZ TEmpty;                                                      (* [comment removed for export] *)
    sb_uar ] ++ rt_rgs ++ relro_rgs.
Definition msb_F : list fact := FMod RA 1 0 :: spsh_fact 64 :: FRange SPSH (SHB + KHI / 8) (SHB + KTOP / 8) :: FRange (laddc SP 256) KHI KTOP :: rt_facts ++ stack_facts 2208.
Definition msb_P0 (o n : Z) : sst := SST 0x60644 (msb_R0 o n) (msb_RGS false o n) msb_F 200 RNone.
Definition msb_Q (o n : Z) : sst := SST 0 (regs_keep (msb_R0 o n) 31 200 TEmpty) (msb_RGS true o n) msb_F 240 RNone.
Definition MSB32_P0 : sst := msb_P0 104 32.  Definition MSB32_Q : sst := msb_Q 104 32.
Definition MSB27_P0 : sst := msb_P0 72 27.   Definition MSB27_Q : sst := msb_Q 72 27.
Lemma MSB_wf : state_wf MSB32_P0 = true /\ state_wf MSB32_Q = true /\ state_wf MSB27_P0 = true /\ state_wf MSB27_Q = true /\
  shape_eqb (s_rgs MSB32_P0) (s_rgs MSB32_Q) = true /\ shape_eqb (s_rgs MSB27_P0) (s_rgs MSB27_Q) = true.
Proof. vm_compute. repeat split. Qed.
