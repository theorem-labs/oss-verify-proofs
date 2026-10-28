(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk SysStep ITree. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_sec_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition mod_entry : Z := 0x1d8100.
Definition mod_retA : Z := 0x1d8188.          (* [comment removed for export] *)
Definition sec_mmap_ecall : Z := 0x1d6824.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mod_frame (m : mem) (sp : word) (ra s0 s1 s2 : word) : Prop :=
  exists junk, rw_cells ctasegs m (bv_unsigned sp - 48) [CB 12 junk; C4 (Z_to_bv 64 34); C8 s2; C8 s1; C8 s0; C8 ra].

Definition mod_regs (ra sp gp tp t0 t1 t2 a6 : word) (size : Z) (name s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR (Z_to_bv 64 mod_retA) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 name (Z_to_bv 64 (roundup4k size))
      (Z_to_bv 64 0) (Z_to_bv 64 (roundup4k size)) (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6
      (Z_to_bv 64 222) (Z_to_bv 64 0x701ae0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition mod_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (size : Z) (name : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (mod_regs ra sp gp tp t0' t1' t2' a6' size name s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ mod_frame m' sp ra s0 s1 s2
    /\ stk ctasegs m' lo (bv_unsigned sp - 48)
    /\ mm_gcells m'.

Lemma mod_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (size : Z) (name : word) (lo : Z),
  (0 < size)%Z -> (size + 8192 <= 2^47)%Z ->
  bv_unsigned name <> 0%Z ->
  mm_gcells m ->
  stk ctasegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 320)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (mod_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc size name lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 size) name a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 mod_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros Hs Hend Hname (G1 & G2 & G3 & G4 & G5) ST HLOH HLO2 HSP MI.
  unfold kHighShadowEnd in *. unfold mod_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  do 6 zstep.
  do 5 zstep. ifT.
  do 3 zstep. ifF.
  do 4 zstep.
  rewrite land_pgmask by lia. fold (roundup4k size).
  zstep. zstep; fix_lit_store.
  do 4 zstep.
  carve_frame 272%nat ST.
  do 8 (zstep; try fix_lit_store).
  do 3 zstep. ifF.
  do 6 zstep. ifT.
  do 10 zstep.
  release_frame FR0 ST (bv_unsigned sp + -48)%Z.
  zstep. rewrite (sx32_small_A 34) by lia.
  do 7 zstep.
  step_ecall.
  unfold mod_A_post, mod_frame, mod_regs.
  do 9 eexists. split; [reflexivity|].
  split; [|split; [|split; [|split; [|split]]]]; try eassumption.
  - replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia. eexists. exact FR.
  - unfold mm_gcells. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Definition mod_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P size lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(P, P + roundup4k size); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' P [CB (Z.to_nat (roundup4k size)) (repeat (Z_to_bv 8 0) (Z.to_nat (roundup4k size)))]
    /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ mm_gcells m'.

Lemma mod_B_spec : forall ra sp gp tp t0 t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o : word) (P size : Z) (name : word) (lo : Z),
  (0 < P)%Z -> (0 < size)%Z -> (P + roundup4k size <= lo)%Z ->
  hide (P + roundup4k size <= img_hull_lo \/ img_hull_hi <= P)%Z ->
  mod_frame m sp ra s0o s1o s2o ->
  mm_gcells m ->
  stk ctasegs m lo (bv_unsigned sp - 48) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (mod_B_post ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P size lo m)
    (nret (MSsvc (mod_regs ra sp gp tp t0 t1 t2 a6 size name s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None m (seg_rom ctasegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k size))])).
Proof.
  intros until lo. intros HP Hs Hend HOUT (junk & FR) (G1 & G2 & G3 & G4 & G5) ST HLOH HLO2 HSP MI.
  unfold kHighShadowEnd in *.
  pose proof (roundup4k_facts size ltac:(lia)) as [RU1 RU2].
  pose proof (munch_refl [(P, P + roundup4k size); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  rewrite nret_MSsvc. unfold mod_regs. rewrite mkR_set_a0, apply_mem_zeros.
  assert (RO : forall x : word, (P <= bv_unsigned x < P + roundup4k size)%Z -> ro_addr ctasegs x = false).
  { intros x Hx. apply ro_free_out. unfold hide in HOUT. lia. }
  unfold hide in HOUT. unfold img_hull_lo, img_hull_hi in HOUT.
  sys_mem_zeros.
  unfold sec_mmap_ecall, mod_retA in *.
  replace (Z_to_bv 64 0x1d6824 + Z_to_bv 64 4 : word) with (Z_to_bv 64 0x1d6828 : word) by (rewrite lit_add_lit; reflexivity).
  zhide.
  zstep.
  do 3 zstep.
  do 3 zstep. ifT.
  do 2 zstep.
  do 2 zstep. zstep; try fix_lit_store.
  do 3 zstep.
  do 3 zstep. ifT.
  do 2 zstep.
  rewrite (proj2 (Z.ltb_ge 18446744073709547520 P)) by lia. cbn [Z.b2z].
  zstep. ifF.
  do 2 zstep.
  do 4 zstep. ifT.
  zstep.
  zstep.
  do 5 zstep.
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  all: try (unfold mm_gcells; repeat (split; [assumption|]); assumption).
Qed.

(* [comment removed for export] *)
Definition uod_entry : Z := 0x1d8084.
Definition uod_retA : Z := 0x1d80b4.
Definition sec_munmap_ecall : Z := 0x1d6830.

Definition uod_frame (m : mem) (sp : word) (ra s0 s1 s2 : word) : Prop :=
  exists junk, rw_cells ctasegs m (bv_unsigned sp - 48) [CB 16 junk; C8 s2; C8 s1; C8 s0; C8 ra].

Definition uod_regs (ra sp gp tp t0 t1 t2 : word) (addr size : Z) (a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    : bvmap 5 word :=
  mkR (Z_to_bv 64 uod_retA) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 size) a2
      (Z_to_bv 64 addr) (Z_to_bv 64 size) a2 a3 a4 a5 a6
      (Z_to_bv 64 215) (Z_to_bv 64 addr) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition uod_A_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (addr size lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem),
    ms' = MSsvc (uod_regs ra sp gp tp t0 t1 t2 addr size a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ uod_frame m' sp ra s0 s1 s2
    /\ stk ctasegs m' lo (bv_unsigned sp - 48).

Lemma uod_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z),
  (0 < addr < 2^64)%Z -> (0 < size < 2^64)%Z -> a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (uod_A_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc addr size lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uod_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros Ha Hs -> -> ST HLO2 HSP MI.
  unfold uod_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  do 6 zstep. ifF.
  zstep. zstep. ifF.
  do 4 zstep.
  zstep.
  step_ecall.
  unfold uod_A_post, uod_frame, uod_regs.
  eexists. split; [reflexivity|].
  split; [|split; [|split; [|split]]]; try eassumption.
  replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia. eexists. exact FR.
Qed.

(* [comment removed for export] *)
Definition uod_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(addr, addr + size); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono_but addr (addr + size) m m'
    /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ mm_gcells m'.

Lemma uod_B_spec : forall ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s0o s1o s2o : word) (addr size lo : Z),
  (0 < addr)%Z -> (0 < size)%Z -> (addr + size <= lo)%Z ->
  hide (addr + size <= img_hull_lo \/ img_hull_hi <= addr)%Z ->
  uod_frame m sp ra s0o s1o s2o ->
  mm_gcells m ->
  stk ctasegs m lo (bv_unsigned sp - 48) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (uod_B_post ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m)
    (nret (MSsvc (uod_regs ra sp gp tp t0 t1 t2 addr size a2 a3 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) fc None m (seg_rom ctasegs))
          (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 size)] [] [])).
Proof.
  intros until lo. intros HA Hs Hend HOUT (junk & FR) (G1 & G2 & G3 & G4 & G5) ST HLOH HLO2 HSP MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(addr, addr + size); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  rewrite nret_MSsvc. unfold uod_regs. rewrite mkR_set_a0, apply_mem_unmaps.
  unfold hide in HOUT. unfold img_hull_lo, img_hull_hi in HOUT.
  sys_mem_unmaps_but WB.
  pose proof (wmono_refl ctasegs m0) as WM.
  unfold sec_munmap_ecall, uod_retA in *.
  replace (Z_to_bv 64 0x1d6830 + Z_to_bv 64 4 : word) with (Z_to_bv 64 0x1d6834 : word) by (rewrite lit_add_lit; reflexivity).
  zhide.
  zstep.
  do 2 zstep. zstep; try fix_lit_store.
  do 2 zstep.
  do 3 zstep. ifT.
  do 2 zstep.
  zstep. ifF.
  do 2 zstep.
  do 4 zstep. ifT.
  zstep.
  do 5 zstep.
  replace (bv_unsigned sp - 48 + 48)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  all: try (eapply wmono_but_trans_r; [exact WB | exact WM]).
  all: try (unfold mm_gcells; repeat (split; [assumption|]); assumption).
Qed.
