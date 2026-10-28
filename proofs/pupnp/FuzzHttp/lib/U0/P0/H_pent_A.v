(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_scanner_get_token H_vfmatch_A H_vfmatch_F H_vfmatch_G1 H_match H_membuffer_delete H_UpnpPrintf H_entity_read_method H_presp_B HU_list_kit HU_pent_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parse_entity_entry := 0x15704%Z.
Notation FMT_CHUNK := 0x1035b%Z.
Notation FMT_CRLF := 0x10541%Z.
Notation JT_ENT := 0x108dc%Z.
Notation GOT_GMAX := 0x2a120%Z.
Notation GMAXA := 0x2b470%Z.
Notation STR_FILE := 0x102a7%Z.
Notation STR_CHUNKMSG := 0x102ed%Z.
Ltac sstep := step; fix_lit_store.

Definition peFS (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation SCc S MB cur := ([C8 (wz MB); C8 (wz cur); C4 (wz 0)]).

Lemma zx32_lit : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Lemma le8_read : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w B.
  assert (L : (Z.to_nat 0 + 8 <= length (le8 w))%nat) by (rewrite length_le8; cbn; lia).
  pose proof (bytes_at_read rsegs m a (le8 w) 0 8 B ltac:(lia) L) as RD.
  rewrite Z.add_0_r in RD. exact RD.
Qed.

Section SEGS.
Context {HCEIL : HasCeiling}.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 144 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^63)%Z.

  Definition peFX (m : mem) : Prop :=
    rw_cells rsegs m q [C8 (wz STR_CHUNKMSG); C8 (wz STR_FILE)] /\ (exists j16, rw_cells rsegs m (q + 16) [CB 4 j16])
    /\ (exists cz, rw_cells rsegs m (q + 20) [C4 cz]) /\ (exists a b, rw_cells rsegs m (q + 24) [C8 a; C8 b]).

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz MB) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz FMT_CHUNK) (wz JT_ENT) (wz GMAXA) (wz FMT_CRLF) s7 (wz 5) (wz 6) (wz 4) (wz 4294967295) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  #[using="QLO LO0 QP PHI"] Lemma pe_entry : forall ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    (P mod 8 = 0)%Z -> stk rsegs m lo (q + 144) -> mem_inv rsegs m ->
    bytes_at rsegs m GOT_GMAX (le8 (wz GMAXA)) ->
    evt rsegs (fun ms' => exists m' a0' a1' a2' a3' a4' a5',
        ms' = PRS 0x157b0 ra t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 a7 (wz S) s7 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(q, q + 144)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo q /\ peFX m'
        /\ rw_cells rsegs m' (q + 40) (peFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra (wz (q + 144)) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_entity_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros PAL ST MI GOT. unfold parse_entity_entry.
    pose proof (munch_refl [(q, q + 144)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (E : bv_unsigned (wz (q + 144)) = q + 144) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 144%nat ST. rewrite !E in *.
    replace (q + 144 + -144)%Z with q in FR by lia. replace (q + 144 + -144)%Z with q in ST by lia.
    do 14 sstep. ub_null.
    pose proof (le8_read _ _ _ GOT) as RD.
    zstep. ub_align. do 14 zstep. zstep.
    zstep. sstep. zstep. sstep. zstep. zstep. zstep.
    name_junk FR. splitcb FR 2%nat [4; 4; 16]%nat. name_junk FR.
    recell FR 3%nat. splitcb FR 4%nat [8; 8]%nat. recell FR 4%nat. recell FR 5%nat.
    split_chunk FR 2%nat Q0 R1. split_chunk R1 1%nat Q16 R2. split_chunk R2 1%nat Q20 R3. split_chunk R3 2%nat Q24 FSH.
    apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { split; [exact Q0|]. split; [eexists; exact Q16|]. split; [eexists; exact Q20| do 2 eexists; exact Q24]. }
    exact FSH.
  Qed.

  #[using="Type"] Lemma pe_head : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r <= 6)%Z ->
    evt rsegs (fun ms' =>
        (r <> 6 /\ ms' = PRS 0x15a58 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m)
        \/ (r = 6 /\ ms' = PRS 0x157b0 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x157ac x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - apply evt_done. right. split; [lia| reflexivity].
  Qed.

  Definition pe_target (e : Z) : Z :=
    if (e =? 1)%Z then 0x157a4 else if (e =? 2)%Z then 0x15940 else if (e =? 3)%Z then 0x157d0
    else if (e =? 4)%Z then 0x158fc else if (e =? 5)%Z then 0x15834 else if (e =? 6)%Z then 0x15968 else 0x159c4.

  Definition ctl9 (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

  #[using="Type"] Lemma pe_dispatch : forall (err hack pos entp clen csz esp : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) -> (0 <= entp <= 6)%Z ->
    evt rsegs (fun ms' => exists a0', ms' = PRS (pe_target entp) x1 t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x157b0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI CTL ER. unfold ctl9 in CTL. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold pe_target.
    assert (CASES : (entp = 0 \/ entp = 1 \/ entp = 2 \/ entp = 3 \/ entp = 4 \/ entp = 5 \/ entp = 6)%Z) by lia.
    destruct CASES as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [Z.eqb Pos.eqb].
    { zstep. rewrite ?sx32_lit by lia. zstep. zstep. if_cases K; zify_cond K.
      - apply evt_done; eexists; reflexivity.
      - exfalso. clear - K. lia. }
    all: zstep; rewrite ?sx32_lit by lia; zstep; zstep; if_cases K; zify_cond K;
         [ exfalso; clear - K; lia
         | zstep; zstep; zstep; zstep; zstep; apply evt_done; eexists; reflexivity ].
  Qed.

  #[using="QLO"] Lemma pe_epi : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 40) (peFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> peFX m ->
    evt rsegs (fun ms' => ms' = MS (mkR ra (wz (q + 144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom rsegs)
                          /\ stk rsegs m lo (q + 144))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (wz 0x15a58) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX. unfold peFS in FSH.
    destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 13 zstep. zstep. zstep.
    eapply stk_release in Q0; [| exact ST| lia]. clear ST. release_all_ lo.
    apply evt_done. split; [reflexivity|]. lazymatch goal with H : stk rsegs m lo _ |- _ => exact H end.
  Qed.

  #[using="Type"] Lemma pe_default : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x15a58 x1 t0 t1 t2 (wz 3) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x159c4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma pe_germ : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS germ_entry (wz 0x157ac) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x157a4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. unfold germ_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="PHI"] Lemma pe_until : forall (A len cap cur esp isreq maj min err hack pos entp clen csz : Z) (eb el pad : word) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m MB (mbuf_cells A len cap) -> rw_cells rsegs m S (SCc S MB cur) ->
    rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] -> rw_cells rsegs m (P + 384) [C8 eb; C8 el] ->
    rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) ->
    (0 <= esp <= len)%Z -> (len < 2^62)%Z -> (0 < A)%Z -> (0 <= cap)%Z -> (A + cap + 1 < 2^63)%Z -> (0 <= cur)%Z ->
    evt rsegs (fun ms' => exists m' a1' a2' a3' a4', ms' = PRS 0x15a58 x1 t0 t1 t2 (wz 2) a1' a2' a3' a4' a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 384, P + 400); (P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' MB (mbuf_cells A len cap) /\ rw_cells rsegs m' S (SCc S MB len)
        /\ rw_cells rsegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] /\ rw_cells rsegs m' (P + 384) [C8 (wz (A + esp)); C8 (wz (len - esp))]
        /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen csz esp))
      (PRS 0x158fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI MBC SC K3 ENT ESP HE HL HA HCP HC HCU. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, ctl9 in *.
    pose proof (munch_refl [(P + 384, P + 400); (P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pe_walk_to 0x15a58. try replace (esp + A)%Z with (A + esp)%Z in * by lia.
    apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="QLO QP PHI"] Lemma pe_clen : forall (A len cap cur esp isreq maj min err hack pos entp clen csz : Z) (eb el pad : word) (bs : list byte)
      gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m MB (mbuf_cells A len cap) ->
    rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] -> rw_cells rsegs m (P + 384) [C8 eb; C8 el] ->
    rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) ->
    ((clen < len - esp)%Z -> (0 < A)%Z /\ (A + (cap + 1) <= lo)%Z /\ rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs]) ->
    (0 <= esp <= len)%Z -> (len <= cap)%Z -> (cap + 1 <= 2^26 + 16)%Z -> (0 < A)%Z -> (A + cap + 1 < 2^63)%Z -> (0 <= clen < 2^32)%Z -> (0 <= pos < 2^31)%Z ->
    evt rsegs (fun ms' => exists m' (r pos' el' : Z) (eb' : word) (bs' : list byte) a0' a1' a2' a3',
        ms' = PRS 0x15a58 x1 t0 t1 t2 a0' a1' a2' a3' a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m' /\ a0' = wz r
        /\ ( (bs' = bs /\ munch [(P + 384, P + 400); (P + 448, P + 452)]%Z m m')
           \/ ((clen < len - esp)%Z /\ bs' = set_byte bs (Z.to_nat (esp + clen)) (Z_to_bv 8 0)
               /\ munch [(P + 384, P + 400); (P + 448, P + 452); (A + (esp + clen), A + (esp + clen) + 1)]%Z m m'
               /\ rw_cells rsegs m' A [CB (Z.to_nat (cap + 1)) bs']) )
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' MB (mbuf_cells A len cap)
        /\ rw_cells rsegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] /\ rw_cells rsegs m' (P + 384) [C8 eb'; C8 (wz el')]
        /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos' entp clen csz esp)
        /\ length bs' = length bs /\ nth_error bs' (Z.to_nat len) = nth_error bs (Z.to_nat len)
        /\ ( (r = 1 /\ pos' = pos /\ eb' = eb /\ el' = len - esp /\ len - esp < clen)
           \/ (r = 0 /\ pos' = 4 /\ eb' = wz (A + esp) /\ el' = clen /\ clen <= len - esp) )%Z)
      (PRS 0x15940 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI MBC VER ENT CTL BLKC ESP LC CMX A0 AHI0 CL POS. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, ctl9 in *.
    pose proof (wmono_refl rsegs m) as WM.
    destruct (Z.lt_ge_cases clen (len - esp)) as [LT|GE].
    2:{
        pose proof (munch_refl [(P + 384, P + 400); (P + 448, P + 452)]%Z m) as MU.
        pe_walk_to 0x15a58.
        if_cases K1; zify_cond K1.
        2:{ pe_walk_to 0x15a58. try replace (esp + A)%Z with (A + esp)%Z in * by lia.
            apply evt_done. eexists. exists 1, pos, (len - esp)%Z, eb, bs. do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
            split. { left. split; [reflexivity| exact MU]. } split; [exact WM|]. split; [exact MI|].
            repeat (split; [eassumption|]). split; [reflexivity|]. split; [reflexivity|].
            left. repeat split; lia. }
        pe_walk_to 0x15a58. try replace (esp + A)%Z with (A + esp)%Z in * by lia.
        apply evt_done. eexists. exists 0, 4, clen, (wz (A + esp)), bs. do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
        split. { left. split; [reflexivity| exact MU]. } split; [exact WM|]. split; [exact MI|].
        repeat (split; [eassumption|]). split; [reflexivity|]. split; [reflexivity|].
        right. repeat split; lia. }
    destruct (BLKC LT) as (A0' & AHI & BLK).
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    pose proof (munch_refl [(P + 384, P + 400); (P + 448, P + 452); (A + (esp + clen), A + (esp + clen) + 1)]%Z m) as MU.
    pe_walk_to 0x15a58.
    -
      set (k := (esp + clen)%Z). assert (Hk : k = (esp + clen)%Z) by reflexivity. clearbody k.
      remember (A + k)%Z as V eqn:EV.
      apply (rw_cells_split_CB rsegs _ A [] (Z.to_nat (cap + 1)) bs [] [Z.to_nat k; 1%nat; Z.to_nat (cap + 1 - k - 1)]) in BLK; [| cbn; lia].
      cbn [app mk_CB_cells] in BLK.
      lazymatch type of BLK with rw_cells _ ?mm _ [?c1; ?c2; ?c3] =>
        destruct (proj1 (rw_cells_app rsegs mm A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
      cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia. rewrite <- EV in BLK23.
      pe_name_reg_val V.
      sstep. subst V.
      pe_walk_to 0x15a58. try replace (esp + A)%Z with (A + esp)%Z in * by lia.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (BLK : rw_cells rsegs mm A [CB (Z.to_nat (cap + 1)) (set_byte bs (Z.to_nat k) (Z_to_bv 8 0))]) end.
      { unfold set_byte.
        lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
          pose proof (proj2 (rw_cells_app rsegs mm A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] [c2; c3])) as J;
          cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
          specialize (J (conj BLK1 BLK23)); cbn [app] in J;
          pose proof (rw_cells_merge rsegs mm A [] [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); c2; c3] []) as M
        end.
        rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
        replace (Z.to_nat k + Datatypes.S (Z.to_nat (cap + 1 - k - 1) + 0))%nat with (Z.to_nat (cap + 1)) in M by lia.
        replace (firstn (Z.to_nat (cap + 1 - k - 1)) (skipn 1 (skipn (Z.to_nat k) bs))) with (skipn (Z.to_nat k + 1) bs) in *.
        2:{ rewrite skipn_skipn. replace (1 + Z.to_nat k)%nat with (Z.to_nat k + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
        pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
      clear BLK1 BLK23.
      apply evt_done. eexists. exists 0, 4, clen, (wz (A + esp)), (set_byte bs (Z.to_nat k) (Z_to_bv 8 0)). do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
      split. { right. split; [lia|]. split; [rewrite Hk; reflexivity|]. split; [first [exact MU | rewrite <- Hk in MU; exact MU | rewrite Hk; exact MU]| exact BLK]. }
      split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). split; [apply set_byte_length; lia|]. split; [apply set_byte_other; lia|].
      right. repeat split; lia.
  Qed.

  #[using="Type"] Lemma pe_chunk1 : forall (cur : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> (0 <= cur < 2^64)%Z ->
    evt rsegs (fun ms' => ms' = PRS match_entry (wz 0x157e8) t0 t1 t2 (wz S) (wz FMT_CHUNK) (wz (q + 20)) (wz (q + 24)) a4 a5 a6 a7 (wz S) (wz cur) t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x157d0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CUR. unfold match_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="QP PHI"] Lemma pe_chunk2 : forall (r v cur sp0 csz esp err hack pos entp clen : Z) (pv : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m (q + 20) [C4 pv] ->
    rw_cells rsegs m q [C8 (wz STR_CHUNKMSG); C8 (wz STR_FILE)] -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) ->
    (0 <= r <= 5)%Z -> (r = 4 -> pv = wz v /\ 0 <= v < 2^31)%Z -> (0 <= sp0 <= cur)%Z -> (cur < 2^62)%Z ->
    evt rsegs (fun ms' => exists m', (
         ( r <> 4 /\ ms' = PRS UpnpPrintf_entry (wz 0x158c8) t0 t1 t2 (wz 2) (wz 7) (wz STR_FILE) (wz 1786) (wz STR_CHUNKMSG) a5 a6 a7 (wz S) (wz r) t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 488, P + 496)]%Z m m' /\ rw_cells rsegs m' S (SCc S MB sp0) /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen csz esp) )
      \/ ( r = 4 /\ ms' = PRS membuffer_delete_entry (wz 0x15808) t0 t1 t2 (wz MB) (wz sp0) (wz (cur - sp0)) a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 464, P + 472)]%Z m m' /\ rw_cells rsegs m' S (SCc S MB cur) /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen v esp) ) )
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rw_cells rsegs m' (q + 20) [C4 pv] /\ rw_cells rsegs m' q [C8 (wz STR_CHUNKMSG); C8 (wz STR_FILE)])
      (PRS 0x157e8 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CZ Q0 CTL RR VR SPR CUR. unfold ctl9, UpnpPrintf_entry, membuffer_delete_entry in *.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    -   pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU.
      sstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists. split; [left; split; [lia| split; [reflexivity| split; [exact MU| split; assumption]]]|].
      split; [exact WM|]. split; [exact MI|]. split; assumption.
    - destruct (VR ltac:(lia)) as [Epv VR']. rewrite Epv in CZ |- *. pose proof (munch_refl [(P + 464, P + 472)]%Z m) as MU.
      zstep. rewrite (sx32_lit v) by lia. zstep. sstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists. split; [right; split; [lia| split; [reflexivity| split; [exact MU| split; assumption]]]|].
      split; [exact WM|]. split; [exact MI|]. split; assumption.
  Qed.

  #[using="Type"] Lemma pe_chunk3 : forall (r : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x157ac x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v (wz r) t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x158c8 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz r) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="lo QLO LO0 QP PHI"] Lemma pe_chunk4 : forall (v cur sp0 esp err hack pos entp clen gmax isreq maj min : Z) (eb el pad : word)
      gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen v esp) ->
    rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] -> rw_cells rsegs m (P + 384) [C8 eb; C8 el] ->
    rw_cells rsegs m GMAXA [C8 (wz gmax)] ->
    (0 <= v < 2^31)%Z -> (0 <= esp <= sp0)%Z -> (sp0 < 2^62)%Z -> (0 <= cur < 2^64)%Z -> (0 < gmax < 2^32)%Z -> (0 <= err < 2^31)%Z -> (0 <= entp < 2^31)%Z ->
    evt rsegs (fun ms' => exists m' (r err' entp' : Z) (el' : cell) a0' a1',
        ms' = PRS 0x157ac x1 t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m' /\ a0' = wz r
        /\ munch [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' S (SCc S MB sp0) /\ rw_cells rsegs m' (P + 440) (ctl9 err' hack pos entp' clen v esp)
        /\ rw_cells rsegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] /\ rw_cells rsegs m' (P + 384) [C8 eb; el']%list
        /\ rw_cells rsegs m' GMAXA [C8 (wz gmax)]
        /\ ( (v = 0 /\ r = 6 /\ err' = err /\ entp' = 6 /\ el' = C8 (wz (sp0 - esp)))
           \/ (1 <= v <= gmax /\ r = 6 /\ err' = err /\ entp' = 5 /\ el' = C8 el)
           \/ (gmax < v /\ r = 3 /\ err' = 413 /\ entp' = entp /\ el' = C8 el) )%Z)
      (PRS 0x15808 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CTL VER ENT GM VR ESP SP0 CUR GMX ERR ENTP. unfold ctl9 in *.
    pose proof (munch_refl [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. sstep. zstep. if_cases K0; zify_cond K0; condn K0.
    -   zstep. zstep. zstep. zstep. zstep. sstep. sstep. zstep.
      apply evt_done. eexists. exists 6, err, 6. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      replace (sp0 - esp + 0)%Z with (sp0 - esp)%Z by lia.
      repeat (split; [eassumption|]). left. repeat split; try lia; try reflexivity.
    - zstep. zstep. if_cases K1; zify_cond K1; condn K1. { exfalso; lia. }
      zstep. zstep. if_cases K2; zify_cond K2.
      +   sstep. zstep. zstep.
        apply evt_done. eexists. exists 6, err, 5. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        repeat (split; [eassumption|]). right; left. repeat split; try lia; try reflexivity.
        revert K2. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
      + zstep. sstep. zstep. zstep.
        apply evt_done. eexists. exists 3, 413, entp. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        repeat (split; [eassumption|]). right; right. repeat split; try lia; try reflexivity.
        revert K2. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="PHI"] Lemma pe_body1 : forall (A len cap cur v esp err hack pos entp clen : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m MB (mbuf_cells A len cap) ->
    rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen v esp) ->
    (0 <= cur <= len)%Z -> (len < 2^62)%Z -> (0 <= v < 2^31)%Z -> (0 <= A)%Z -> (A + cap + 1 < 2^63)%Z ->
    evt rsegs (fun ms' => exists m' a1',
        ( (len - cur < v)%Z /\ ms' = PRS 0x15a58 x1 t0 t1 t2 (wz 1) a1' a2 a3 a4 a5 a6 a7 (wz S) (wz cur) t3 t4 t5 t6 gp tp F fc m' /\ m' = m
          /\ rw_cells rsegs m' S (SCc S MB cur) )
        \/ ( (v <= len - cur)%Z /\ ms' = PRS match_entry (wz 0x1585c) t0 t1 t2 (wz S) (wz FMT_CRLF) a2 a3 a4 a5 a6 a7 (wz S) (wz (cur + v)) t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
           /\ rw_cells rsegs m' S (SCc S MB (cur + v)) /\ rw_cells rsegs m' MB (mbuf_cells A len cap) /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen v esp) ))
      (PRS 0x15834 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC MBC CTL CUR HL VR HA HC. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, ctl9, match_entry in *.
    pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; condn K.
    -   zstep. zstep. apply evt_done. do 2 eexists. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity| exact SC].
    - zstep. sstep. zstep. zstep. zstep.
      replace (v + cur)%Z with (cur + v)%Z in * by lia.
      apply evt_done. do 2 eexists. right. split; [lia|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). eassumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="PHI"] Lemma pe_body2 : forall (r cur sp0 v esp err hack pos entp clen : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen v esp) ->
    (0 <= r <= 5)%Z -> (0 <= v <= sp0)%Z -> (sp0 <= cur < 2^62)%Z ->
    evt rsegs (fun ms' => exists m' a1' a2',
        ( r <> 4 /\ ms' = PRS 0x15a58 x1 t0 t1 t2 (wz r) a1' a2' a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
           /\ rw_cells rsegs m' S (SCc S MB (cur - v)) /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen v esp) )
        \/ ( r = 4 /\ ms' = PRS membuffer_delete_entry (wz 0x15874) t0 t1 t2 (wz MB) (wz sp0) (wz (cur - sp0)) a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m' /\ m' = m ))
      (PRS 0x1585c x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CTL RR VR CUR. unfold ctl9, membuffer_delete_entry in *.
    pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - zstep. zstep. zstep. sstep. zstep.
      apply evt_done. do 3 eexists. left. split; [lia|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; assumption.
    - zstep. zstep. zstep. zstep. zstep.
      apply evt_done. do 3 eexists. right. split; [lia|]. split; [reflexivity| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="lo QLO LO0 QP PHI"] Lemma pe_body3 : forall (v cur sp0 esp err hack pos entp clen gmax el : Z) (eb : word)
      gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen v esp) ->
    rw_cells rsegs m (P + 384) [C8 eb; C8 (wz el)] -> rw_cells rsegs m GMAXA [C8 (wz gmax)] ->
    (0 <= v < 2^31)%Z -> (0 <= sp0 < 2^62)%Z -> (0 <= cur < 2^64)%Z -> (0 < gmax < 2^32)%Z -> (0 <= el <= gmax)%Z -> (0 <= err < 2^31)%Z -> (0 <= entp < 2^31)%Z ->
    evt rsegs (fun ms' => exists m' (r err' entp' : Z) a0' a1' a2' pc,
        ms' = PRS pc x1 t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m' /\ a0' = wz r
        /\ munch [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' S (SCc S MB sp0) /\ rw_cells rsegs m' (P + 440) (ctl9 err' hack pos entp' clen v esp)
        /\ rw_cells rsegs m' (P + 384) [C8 eb; C8 (wz (el + v))] /\ rw_cells rsegs m' GMAXA [C8 (wz gmax)]
        /\ ( (el + v <= gmax /\ pc = 0x157ac /\ r = 6 /\ err' = err /\ entp' = 3)
           \/ (gmax < el + v /\ pc = 0x15a58 /\ r = 3 /\ err' = 413 /\ entp' = entp) )%Z)
      (PRS 0x15874 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) (wz sp0) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CTL ENT GM VR SP0 CUR GMX EL ERR ENTP. unfold ctl9 in *.
    pose proof (munch_refl [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. rewrite ?sx32_lit by lia. zstep. zstep. sstep. zstep. sstep.
    replace (v + el)%Z with (el + v)%Z in * by lia.
    zstep. if_cases K1; zify_cond K1; condn K1. { exfalso; lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    -   zstep. sstep. zstep. zstep.
      apply evt_done. eexists. exists 3, 413, entp. do 4 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). right. repeat split; try lia.
      revert K2. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    - sstep. sstep. zstep. zstep.
      apply evt_done. eexists. exists 6, err, 3. do 4 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). left. repeat split; try lia.
      revert K2. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma pe_hdr1 : forall (cur : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> (0 <= cur < 2^64)%Z ->
    evt rsegs (fun ms' => ms' = PRS 0x14c4c (wz 0x15974) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 (wz cur) s7 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x15968 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CUR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="PHI"] Lemma pe_hdr2 : forall (r cur sp0 err hack pos entp clen csz esp : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) ->
    (0 <= r <= 5)%Z -> (0 <= sp0 <= cur)%Z -> (cur < 2^62)%Z -> (0 <= pos < 2^31)%Z ->
    evt rsegs (fun ms' => exists m' a1',
        ( r <> 4 /\ ms' = PRS 0x15a58 x1 t0 t1 t2 (wz r) a1' a2 a3 a4 a5 a6 a7 (wz sp0) s7 t3 t4 t5 t6 gp tp F fc m' /\ m' = m )
        \/ ( r = 4 /\ ms' = PRS membuffer_delete_entry (wz 0x15994) t0 t1 t2 (wz MB) (wz sp0) (wz (cur - sp0)) a3 a4 a5 a6 a7 (wz sp0) s7 t3 t4 t5 t6 gp tp F fc m'
            /\ munch [(P + 448, P + 452)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
            /\ rw_cells rsegs m' S (SCc S MB cur) /\ rw_cells rsegs m' (P + 440) (ctl9 err hack 4 entp clen csz esp) ))
      (PRS 0x15974 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz sp0) s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CTL RR SPR CUR POS. unfold ctl9, membuffer_delete_entry in *.
    pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. do 2 eexists. left. split; [lia|]. split; [reflexivity| reflexivity].
    - zstep. sstep. zstep. zstep. zstep. zstep.
      apply evt_done. do 2 eexists. right. split; [lia|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; assumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="PHI"] Lemma pe_hdr3 : forall (A len cap cur sp0 esp err hack pos entp clen csz : Z) (eb el : word)
      gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m MB (mbuf_cells A len cap) ->
    rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) -> rw_cells rsegs m (P + 384) [C8 eb; C8 el] ->
    (0 <= sp0 < 2^64)%Z -> (0 <= cur < 2^64)%Z -> (0 < A)%Z -> (0 <= cap)%Z -> (A + cap + 1 < 2^63)%Z -> (0 <= esp < 2^62)%Z ->
    evt rsegs (fun ms' => exists m' a1' a2', ms' = PRS 0x15a58 x1 t0 t1 t2 (wz 0) a1' a2' a3 a4 a5 a6 a7 (wz sp0) s7 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 384, P + 392); (P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' S (SCc S MB sp0) /\ rw_cells rsegs m' MB (mbuf_cells A len cap)
        /\ rw_cells rsegs m' (P + 440) (ctl9 err hack pos entp clen csz esp) /\ rw_cells rsegs m' (P + 384) [C8 (wz (A + esp)); C8 el])
      (PRS 0x15994 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz sp0) s7 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC MBC CTL ENT SP0 CUR HA HCP HC ESP. unfold ctl9, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
    pose proof (munch_refl [(P + 384, P + 392); (P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pe_walk_to 0x15a58. try replace (esp + A)%Z with (A + esp)%Z in * by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    repeat (split; [eassumption|]). eassumption.
  Qed.
End SEGS.
