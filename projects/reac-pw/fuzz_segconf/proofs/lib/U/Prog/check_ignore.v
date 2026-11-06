From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import check_ignore_c.
Import ListNotations.
Open Scope Z_scope.

(** check_ignore of the UBSan image (0x14b40): the plain walk
    (Prog/check_ignore.v) after the alignment check `andi a2, a1, 3; bnez a2` to the trap `unimp` at 0x14b54, which
    want mod 4 = 0 makes fall through. Then `lw a1, 0x18(a1)` reads want->ignore (flag_enc (ms_ignore g)),
    `bne a0, a1` goes to the abort frame, else `ret`; got = b2z b with Bool.eqb b (ms_ignore g) = true makes the bne
    not taken. Nothing is stored, so the memory is unchanged (W = [], m' = m). *)

(** A 4-byte field of a byte block in memory, as `lw` reads it. *)
Lemma fld4_read : forall segs m a bs off v,
  bytes_at segs m a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  fldz off 4 bs = le4 v ->
  ov_read_bytes segs m (wa (a + off)) 4 = Some (le4 v).
Proof.
  intros segs m a bs off v H Ho Hl E.
  rewrite (bytes_at_read segs m a bs off 4 H Ho) by lia. f_equal. exact E.
Qed.

(** `lw` sign-extends bit 31; a value below 2^31 comes back as itself. *)
Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  assert (E1 : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
  assert (E2 : bv_modulus 32 = 2 ^ 32) by reflexivity.
  unfold bv_swrap, bv_wrap. rewrite E1, E2. rewrite Z.mod_small by lia. lia.
Qed.

Theorem check_ignore_holds : check_ignore_contract.
Proof.
  unfold check_ignore_contract, check_ignore_pre, CHECK_IGNORE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo b g (Hal & (bs & BA & HE) & Hap & Hgot & Heq & ST & MI).
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  destruct HE as (Hlen & _ & _ & _ & Hig & _).
  assert (HL : Z.of_nat (length bs) = 256) by (rewrite Hlen; reflexivity).
  apply Bool.eqb_prop in Heq. unfold flag_enc in Hig. rewrite <- Heq in Hig.
  pose proof (u64_range a0) as R0.
  assert (LA : Z.land (bv_unsigned a1) 3 = 0).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hal. }
  assert (RD : ov_read_bytes rsegs m (wa (bv_unsigned a1 + 24)) 4 = Some (le4 (Z_to_bv 64 (b2z b)))).
  { apply (fld4_read rsegs m _ bs); [exact BA | lia | lia | exact Hig]. }
  assert (Hb : 0 <= b2z b <= 1) by (destruct b; cbn; lia).
  (* andi a2, a1, 3 *)
  zstep. rewrite ?LA.
  (* bnez a2: want mod 4 = 0, the trap is not taken *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; rewrite ?LA in K; lia | idtac ] .. ].
  (* lw a1, 0x18(a1) *)
  zstep.
  rewrite (sx32_small (b2z b)) by lia.
  (* bne a0, a1: a0 = b2z b *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; rewrite ?unsigned_lit in K by lia; lia | idtac ] .. ].
  (* ret *)
  zstep.
  apply evt_done. unfold ret_void. cbv beta.
  do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
  split; [exact (proj1 ST)|exact I].
Qed.
