(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_mmapordie.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition sa_entry : Z := 0x19f7a4.
Definition sa_retA : Z := 0x19f860.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sa_frame (m : mem) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : Prop :=
  exists j, rw_cells asegs m (bv_unsigned sp - 96)
    [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sa_msz_facts : forall SZ, (0 <= SZ)%Z -> (SZ + 4096 <= sa_msz SZ < SZ + 8192 /\ sa_msz SZ mod 4096 = 0)%Z.
Proof.
  intros SZ H. unfold sa_msz. pose proof (roundup4k_facts SZ H) as [R1 R2].
  split; [lia|]. rewrite Z.add_mod, R2 by lia. reflexivity.
Qed.

Definition secalloc_A1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SZ lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0' t1' t2' a6' (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 416, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ sa_frame m' sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    /\ mod_frame m' (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
         (Z_to_bv 64 (sa_msz SZ))
    /\ stk asegs m' lo (bv_unsigned sp - 144)
    /\ mm_gcells m' /\ sec_page m' /\ name_cells m'.

Lemma secalloc_A1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (SZ lo : Z),
  (0 < SZ)%Z -> (SZ + 16384 <= 2^47)%Z ->
  mm_gcells m -> sec_page m -> name_cells m ->
  stk asegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 416)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (secalloc_A1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SZ lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SEC) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SZ) (Z_to_bv 64 8) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sa_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HSZ HSZ2 MM PG NM ST HLOH HLO HSP MI.
  pose proof MM as (G1 & G2 & G3 & G4 & G5). pose proof NM as (N1 & N2).
  unfold sec_page in PG. change i_sec_page with 6722840%Z in PG.
  unfold kHighShadowEnd, sa_entry, sec_name in *. change SEC with 6722840%Z. change GSTAT with 6723464%Z.
  pose proof (roundup4k_facts SZ ltac:(lia)) as [RU1 RU2].
  pose proof (munch_refl [(bv_unsigned sp - 416, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  clear MM NM.
  carve_frame 96%nat ST.
  zhide.
  zidle_begin sp 96%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 3 zstep.
  do 2 zstep.
  zstep. zstep. ifF.
  do 4 zstep. zstep. ifF.
  do 10 zstep.
  rewrite land_pgmask by lia.
  change (Z.land (Z.land (0 + - Z.b2z (4096 <? 8)) 18446744073709551615) 8) with 0%Z.
  replace ((SZ + 4095) / 4096 * 4096 + 4096 + 0)%Z with (sa_msz SZ) by (unfold sa_msz, roundup4k; lia).
  replace ((SZ + 4095) / 4096 * 4096 + 4096)%Z with (sa_msz SZ) by (unfold sa_msz, roundup4k; lia).
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  zstep. ifT.
  do 5 zstep.
  zstep.
  sp_facts.
  call (mod_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (sa_msz SZ) (Z_to_bv 64 191173) lo).
  all: rewrite ?Esp in *; try lia.
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  all: try assumption.
  apply evt_done. unfold secalloc_A1_post. do 9 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [unfold sa_frame; eexists; replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia; eassumption|].
  split; [assumption|].
  split; [replace (bv_unsigned sp - 144)%Z with (bv_unsigned sp + -96 - 48)%Z by lia; assumption|].
  split; [unfold mm_gcells; repeat (split; [assumption|]); assumption|].
  split; [unfold sec_page; assumption| unfold name_cells; split; assumption].
Qed.
