(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rmap_entry : Z := 0x9f230.
Definition rmap_retM : Z := 0x9f25c.
Definition mfi_retB : Z := 0x970a4.
Definition mmap_ecall_pc : Z := 0x952e4.

Definition mfi_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 s4 : word) : Prop :=
  exists junk, rw_cells asegs m (bv_unsigned sp - 96)
    [C4 (Z_to_bv 64 50); CB 44 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition rmap_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 s4 : word) : Prop :=
  (exists junk x0 x1, rw_cells asegs m (bv_unsigned sp - 128)
    [C4 (Z_to_bv 64 50); CB 44 junk; C8 s4; C8 s3; C8 s2; C8 x1; C8 x0; C8 (Z_to_bv 64 rmap_retM)])
  /\ rw_cells asegs m (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra].

Definition mfi_regs (ra sp gp tp : word) (t0 t1 t2 a6 : word) (addr size : Z) (name s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR (Z_to_bv 64 mfi_retB) (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 size) (Z_to_bv 64 1)
      (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 3) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6
      (Z_to_bv 64 222) (Z_to_bv 64 addr) name (Z_to_bv 64 0x2036e0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition rmap_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size : Z) (name : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (mfi_regs ra sp gp tp t0' t1' t2' a6' addr size name s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 400, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rmap_frame m' sp ra s0 s1 s2 s3 s4
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ mm_gcells m'.

Lemma rmap_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size : Z) (name : word) (lo : Z),
  (0 < addr)%Z -> (addr mod 4096 = 0)%Z -> (0 < size)%Z -> (size mod 4096 = 0)%Z -> (addr + size <= 2^47)%Z ->
  bv_unsigned name <> 0%Z ->
  mm_gcells m ->
  stk asegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 400)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (rmap_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size name lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 addr) (Z_to_bv 64 size) name a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Ha Hal Hs Hsal Hend Hname (G1 & G2 & G3 & G4 & G5) ST HLOH HLO2 HSP MI.
  unfold kHighShadowEnd in *. unfold rmap_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zhide.

  carve_frame 32%nat ST.
  do 5 zstep.
  do 6 zstep.

  do 2 zstep.
  carve_frame 96%nat ST.
  zidle_begin sp 128%Z MUz WMz.
  do 9 (zstep; try fix_lit_store).
  zidle_end MUz WMz.
  do 3 zstep.
  do 4 zstep. ifT.
  do 3 zstep. ifF.
  do 5 zstep. ifT.
  do 1 zstep.
  destruct (land_pgmask_aligned addr ltac:(lia) Hal) as [EA _].
  destruct (land_pgmask_aligned size ltac:(lia) Hsal) as [_ ES]. rewrite EA, ES. clear EA ES.
  zstep. zstep; fix_lit_store.
  do 4 zstep.
  carve_frame 272%nat ST.
  do 11 (zstep; try fix_lit_store). ifF.
  do 6 zstep. ifT.
  do 10 zstep.
  release_frame FR1 ST (bv_unsigned sp + -128)%Z.
  zstep. rewrite (sx32_small_A 50) by lia.
  do 7 zstep.
  step_ecall.
  unfold rmap_A_post, rmap_frame, mfi_regs, rmap_retM.
  do 9 eexists. split; [reflexivity|].
  split; [|split; [|split; [|split; [|split]]]]; try eassumption.
  - replace (bv_unsigned sp - 128)%Z with (bv_unsigned sp + -128)%Z by lia.
    replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp + -32)%Z by lia.
    split; [do 3 eexists; exact FR0 | exact FR].
  - unfold mm_gcells. repeat (split; [assumption|]). assumption.
Qed.

Definition mfi_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(addr, addr + size); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ mm_gcells m'.

Lemma mfi_B_spec : forall ra sp gp tp t0 t1 t2 a6 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o s3o s4o : word) (addr size : Z) (name : word) (lo : Z),
  (img_hull_hi <= addr)%Z -> (0 < size)%Z -> (addr + size <= lo)%Z ->
  rmap_frame m sp ra s0o s1o s2o s3o s4o ->
  mm_gcells m ->
  stk asegs m lo (bv_unsigned sp - 128) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 128)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (mfi_B_post ra sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m)
    (nret (MSsvc (mfi_regs ra sp gp tp t0 t1 t2 a6 addr size name s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom asegs))
          (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 size)])).
Proof.
  intros until lo. intros Hlo Hs Hend ((junk & x0 & x1 & FR) & FRM) (G1 & G2 & G3 & G4 & G5) ST HLOH HLO2 HSP MI.
  unfold kHighShadowEnd, img_hull_hi in *.
  pose proof (munch_refl [(addr, addr + size); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  rewrite nret_MSsvc. unfold mfi_regs. rewrite mkR_set_a0, apply_mem_zeros.
  assert (RO : forall x : word, (addr <= bv_unsigned x < addr + size)%Z -> ro_addr asegs x = false).
  { intros x Hx. apply ro_free_range. unfold img_hull_hi. lia. }
  sys_mem_zeros.
  unfold mmap_ecall_pc, mfi_retB, rmap_retM in *.
  replace (Z_to_bv 64 0x952e4 + Z_to_bv 64 4 : word) with (Z_to_bv 64 0x952e8 : word) by (rewrite lit_add_lit; reflexivity).
  zhide.
  zstep.
  do 3 zstep.
  do 2 zstep.
  zstep. ifT.
  do 2 zstep.
  do 3 zstep.
  do 3 zstep.
  do 3 zstep. ifT.
  do 2 zstep.
  rewrite (proj2 (Z.ltb_ge 18446744073709547520 addr)) by lia. cbn [Z.b2z].
  zstep. ifF.
  do 2 zstep.
  do 3 zstep.
  zstep. ifT.
  zstep.
  do 8 zstep.
  replace (bv_unsigned sp - 128 + 96)%Z with (bv_unsigned sp - 32)%Z by lia.
  release_frame FR ST (bv_unsigned sp - 32)%Z.

  zstep.
  replace (ret_pc (Z_to_bv 64 0x9f25c)) with (Z_to_bv 64 0x9f25c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zstep. ifF.
  do 5 zstep.
  replace (bv_unsigned sp - 32 + 32)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FRM ST (bv_unsigned sp).
  zstep.
  finish.
  all: try (unfold mm_gcells; repeat (split; [assumption|]); assumption).
Qed.
