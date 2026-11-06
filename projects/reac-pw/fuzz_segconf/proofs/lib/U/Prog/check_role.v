From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import check_role_c.
Import ListNotations.
Open Scope Z_scope.

(** check_role of the UBSan image (0x14ac4): the plain walk
    (Prog/check_role.v) after the alignment check `andi a3, a2, 3; bnez a3` to the trap `unimp` at 0x14af0, which
    want mod 4 = 0 makes fall through. Then `lw a3, 0x14(a2)` (want->role_set), `bne a0, a3` to the abort frame,
    `beqz a0` to the `ret`, `lw a0, 0x10(a2)` (want->role, sign-extended), `bne a1, a0` to the abort frame, `ret`.
    With Some r: got_set = 1, ms_role_set g = true, got = r = ms_role g < 2^31, so neither bne is taken and the beqz
    falls through; with None: got_set = 0, ms_role_set g = false, so the bne is not taken and the beqz returns.
    Nothing is stored, so the memory is unchanged (W = [], m' = m). *)

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

Theorem check_role_holds : check_role_contract.
Proof.
  unfold check_role_contract, check_role_pre, CHECK_ROLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo o g (Hal & (bs & BA & HE) & Hap & Hset & Hgot & Hok & ST & MI).
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  destruct HE as (Hlen & _ & [[Hr0 Hrole] _] & Hrs & _).
  assert (HL : Z.of_nat (length bs) = 256) by (rewrite Hlen; reflexivity).
  unfold flag_enc in Hrs.
  pose proof (u64_range a0) as R0. pose proof (u64_range a1) as R1.
  assert (LA : Z.land (bv_unsigned a2) 3 = 0).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hal. }
  destruct o as [r|].
  - (* the reader answered Some r *)
    destruct Hgot as [Hgot Hr31].
    apply andb_prop in Hok. destruct Hok as [Hrs1 Hrr]. apply Z.eqb_eq in Hrr.
    rewrite Hrs1 in Hrs. change (if true then 1 else 0) with 1 in Hrs.
    assert (RD1 : ov_read_bytes rsegs m (wa (bv_unsigned a2 + 20)) 4 = Some (le4 (Z_to_bv 64 1))).
    { apply (fld4_read rsegs m _ bs); [exact BA | lia | lia | exact Hrs]. }
    assert (RD2 : ov_read_bytes rsegs m (wa (bv_unsigned a2 + 16)) 4 = Some (le4 (Z_to_bv 64 (ms_role g)))).
    { apply (fld4_read rsegs m _ bs); [exact BA | lia | lia | exact Hrole]. }
    (* andi a3, a2, 3 *)
    zstep. rewrite ?LA.
    (* bnez a3: want mod 4 = 0, the trap is not taken *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; rewrite ?LA in K; lia | idtac ] .. ].
    (* lw a3, 0x14(a2) *)
    zstep.
    rewrite (sx32_small 1) by lia.
    (* bne a0, a3: a0 = 1 *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
    (* beqz a0: a0 = 1 *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
    (* lw a0, 0x10(a2) *)
    zstep.
    rewrite (sx32_small (ms_role g)) by lia.
    (* bne a1, a0: a1 = r = ms_role g *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; rewrite ?unsigned_lit in K by lia; lia | idtac ] .. ].
    (* ret *)
    zstep.
    apply evt_done. unfold ret_void. cbv beta.
    do 16 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    split; [exact (proj1 ST)|exact I].
  - (* the reader answered None *)
    apply Bool.negb_true_iff in Hok. rewrite Hok in Hrs. change (if false then 1 else 0) with 0 in Hrs.
    assert (RD1 : ov_read_bytes rsegs m (wa (bv_unsigned a2 + 20)) 4 = Some (le4 (Z_to_bv 64 0))).
    { apply (fld4_read rsegs m _ bs); [exact BA | lia | lia | exact Hrs]. }
    (* andi a3, a2, 3 *)
    zstep. rewrite ?LA.
    (* bnez a3: want mod 4 = 0, the trap is not taken *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; rewrite ?LA in K; lia | idtac ] .. ].
    (* lw a3, 0x14(a2) *)
    zstep.
    rewrite (sx32_small 0) by lia.
    (* bne a0, a3: a0 = 0 *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
    (* beqz a0: taken to the ret at 0x14ae0 *)
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
