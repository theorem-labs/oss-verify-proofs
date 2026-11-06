From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import check_refusals_c.
Import ListNotations.
Open Scope Z_scope.

(** check_refusals of the UBSan image (0x14bf8): the plain
    walk (Prog/check_refusals.v) after the alignment check `andi a2, a0, 7; andi a3, a1, 3; or a2, a2, a3; bnez a2`
    to the trap `unimp` at 0x14c48, which c mod 16 = 0 and m mod 16 = 0 make fall through. Then a0 = c + 0x34c8,
    a1 = m + 0x2008; `lw a2, 4(a0)` (c->refused) vs `lw a3, 0(a1)` (m->refused) and `lw a0, 0(a0)` (c->n_refusals)
    vs `lw a1, 0x3a4(a1)` (m->n_kept), each `bne` to the abort frame; check_refusals rc mc = true makes each pair the
    same u32 value, so the same word, and neither bne is taken; `ret`. Nothing is stored, so the memory is unchanged
    (W = [], m' = m). *)

(** A 4-byte field of a byte block in memory, as `lw` reads it. *)
Lemma fld4_read : forall segs m a bs off v,
  bytes_at segs m a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  fldz off 4 bs = le4 v ->
  ov_read_bytes segs m (wa (a + off)) 4 = Some (le4 v).
Proof.
  intros segs m a bs off v H Ho Hl E.
  rewrite (bytes_at_read segs m a bs off 4 H Ho) by lia. f_equal. exact E.
Qed.

Theorem check_refusals_holds : check_refusals_contract.
Proof.
  unfold check_refusals_contract, check_refusals_pre, CHECK_REFUSALS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo rc mc
         (Hc0 & Hcal & (bc & BC & HC) & Hcap & Hm0 & Hmal & (bm & BM & HM) & Hmap & Hok & ST & MI).
  pose proof (bytes_at_bound _ _ _ _ BC) as BBc. pose proof (bytes_at_bound _ _ _ _ BM) as BBm.
  destruct HC as (HLc & _ & _ & _ & _ & _ & [Hn0 Hnref] & [Hr0 Hrref] & _).
  destruct HM as (HLm & _ & _ & _ & _ & [Hmr0 Hmref] & _ & _ & _ & [Hmk0 Hmkept] & _).
  unfold SEG_C_SIZE in HLc. unfold SEG_M_SIZE in HLm.
  unfold check_refusals in Hok. apply andb_prop in Hok. destruct Hok as [Href Hlen].
  apply Z.eqb_eq in Href. apply Nat.eqb_eq in Hlen.
  rewrite <- Href in Hmref. rewrite <- Hlen in Hmkept.
  assert (LA0 : Z.land (bv_unsigned a0) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    Z.div_mod_to_equations. lia. }
  assert (LA1 : Z.land (bv_unsigned a1) 3 = 0).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
    Z.div_mod_to_equations. lia. }
  assert (RD1 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 13516)) 4
                = Some (le4 (Z_to_bv 64 (rc_refused rc)))).
  { apply (fld4_read rsegs m _ bc); [exact BC | lia | lia | exact Hrref]. }
  assert (RD2 : ov_read_bytes rsegs m (wa (bv_unsigned a1 + 8200)) 4
                = Some (le4 (Z_to_bv 64 (rc_refused rc)))).
  { apply (fld4_read rsegs m _ bm); [exact BM | lia | lia | exact Hmref]. }
  assert (RD3 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 13512)) 4
                = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))))).
  { apply (fld4_read rsegs m _ bc); [exact BC | lia | lia | exact Hnref]. }
  assert (RD4 : ov_read_bytes rsegs m (wa (bv_unsigned a1 + 9132)) 4
                = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc)))))).
  { apply (fld4_read rsegs m _ bm); [exact BM | lia | lia | exact Hmkept]. }
  (* andi a2, a0, 7; andi a3, a1, 3; or a2, a2, a3 *)
  zstep. rewrite ?LA0. zstep. rewrite ?LA1. zstep.
  (* bnez a2: c and m are 16-aligned, the trap is not taken *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; rewrite ?LA0, ?LA1 in K; lia | idtac ] .. ].
  (* lui a2, 2; lui a3, 3; addiw a2, a2, 8; addiw a3, a3, 0x4c8; add a1, a1, a2; add a0, a0, a3 *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* lw a2, 4(a0); lw a3, 0(a1) *)
  zstep. zstep.
  (* bne a2, a3: both are c->refused = m->refused *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* lw a0, 0(a0); lw a1, 0x3a4(a1) *)
  zstep. zstep.
  (* bne a0, a1: both are n_refusals = n_kept *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* ret *)
  zstep.
  apply evt_done. unfold ret_void. cbv beta.
  do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
  split; [exact (proj1 ST)|exact I].
Qed.
