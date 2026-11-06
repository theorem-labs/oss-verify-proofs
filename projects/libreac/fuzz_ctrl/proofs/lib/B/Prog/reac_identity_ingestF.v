(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths and module names changed; 769 of its 826 lines of code are new or changed and 1009 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_identity_ingest.v, with its module paths and module names changed; 279 of its 812 lines of code are new or changed and 293 lines of the source are left out. *)
(* The footprint twin of reac_identity_ingest.v (image B; RECIPE.md step 1 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, by the script of reac_identity_ingest.v over StepF's step. Each access of the
   run is closed from one rng premise of reac_identity_ingest_contract_F: the stores and loads of the 32-byte frame,
   the two 8-byte loads of the GOT cell and of the runtime cell that holds the shadow offset, the 1-byte load of each
   checked byte of [p, p + len) and of [id, id + 38), the 1- and 2-byte stores inside [id, id + 38), and the 1-byte
   load of the shadow byte of each checked byte ((x >> 3) + ASAN_K, inside the byte-exact shadow span of its range).
   reac_identity_ingest.v and its theorem are unchanged; reac_identity_ingest_holds_of_F re-derives the old statement
   from the footprint form (reac_identity_ingest_contract_of_F, RNG_all). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcIdentModel RcIdentLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  RcAsanRT reac_identity_ingest_c reac_identity_ingest.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* StepF's imports bring Lib/Arr's one-element upd back into scope: the model's list splice (RcIdentModel.upd), as
   in reac_identity_ingest.v, is the one this script's statements use. RcIdentModel defines no tactic, so StepF's
   step / if_cases keep priority. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel.
Import ListNotations.
Open Scope Z_scope.

(* The store hook of the old proof is Lib/Tac's (fix_lit_store, then mem_after_store only when the written object
   has an rw_cells hypothesis): the u16 and u8 stores of this function are normalised to le2 / le1 of a word, which
   the script's rewrites (vs0..vs3, le2_orshl, le1_zxb, le1_lit) need. The same hook on evtF goals. *)
Ltac iiF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac iiF_store :=
  try iiF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= iiF_store.

(* The shadow byte of a checked byte x of [a, b] is inside the byte-exact shadow span of [a, b]; Z.div is opaque to
   lia, so both bounds come from Z.div_le_mono, here in a context with no other division. *)
Lemma iiF_shadow1 : forall RNG K a b x,
  rng RNG (a / 8 + K) (b / 8 - a / 8 + 1) -> a <= x <= b -> rng RNG (x / 8 + K) 1.
Proof.
  intros RNG K a b x H Hx. eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x b 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* reac_identity_ingest.v proves this inside its Section Arms, so the exported lemma carries that section's
   variables (its lia reads their hypotheses) and cannot be rewritten with here: the same statement at top level. *)
Lemma b_ltu_neg_rF : forall x c, 0 <= x < 2^64 -> -2^64 <= c < 0 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 c) = (x <? c + 2^64).
Proof.
  intros x c Hx Hc. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, ii_mod_neg by lia.
  reflexivity.
Qed.

(* reac_identity_ingest.v's kslow / kchk / vsum_reg, matched on evtF goals. *)
Ltac kslowF FAST key pF :=
  repeat (lazymatch goal with
          | |- evtF _ _ _ (MS _ _ pF _ _ _ _) => fail
          | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
              first [ replace c with true by (symmetry; kcond_solve)
                    | replace c with false by (symmetry; kcond_solve) ]; cbv iota
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
          end);
  lazymatch goal with
  | |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
      let v := eval cbv [tget] in (tget key R) in
      lazymatch v with Some ?x => exact (FAST x) end
  end.

Ltac kchkF k OKh rn :=
  let KR := fresh "KR" in pose proof (rc_byte_signed k) as KR;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?sg ?RNG ?Q (MS ?R ?F (if negb (Z.eqb (bv_signed k) 0) then ?pS else ?pF) ?fc ?rv ?m ?ro) =>
      let key := eval vm_compute in (bv_key (Z_to_bv 5 rn)) in
      let FAST := fresh "FAST" in
      assert (FAST : forall z : word, evtF sg RNG Q (MS (tset key z R) F pF fc rv m ro));
      [ let z := fresh "z" in intros z; cbv beta iota fix delta [tset]; clear OKh
      | let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb]; cbv iota;
        [ let v := eval cbv [tget] in (tget key R) in
          lazymatch v with Some ?x => exact (FAST x) end
        | kslowF FAST key pF ] ]
  end.

Ltac vsum_regF pb rn :=
  lazymatch goal with
  | |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
      let key := eval vm_compute in (bv_key (Z_to_bv 5 rn)) in
      let v := eval cbv [tget] in (tget key R) in
      lazymatch v with
      | Some ?x =>
          let EV := fresh "EV" in
          assert (EV : x = Z_to_bv 64 (vsum pb))
            by (clear - pb; vb_ranges pb; unfold vsum, vb; lor_norm; f_equal; lia);
          rewrite EV; clear EV
      end
  end.

Section TopF.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo id ad p len : Z) (idb pb j8 : list byte) (RNG : footprint).
Hypothesis HLO : lo + 32 <= bv_unsigned sp.
Hypothesis RFR : rng RNG (bv_unsigned sp - 32) 32.

Local Abbreviation W := [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)].
Local Abbreviation Post := (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0
                              lo id ad p len idb pb).
Local Abbreviation FC := [CB 8 j8; C8 s1; C8 s0; C8 ra].

(* the frame loads of the epilogue: inside the window premise *)
Lemma ret_atF : forall m r (y5 y6 y7 y8 y9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
  rw_cells rsegs m (bv_unsigned sp + -32) FC ->
  stk rsegs m lo (bv_unsigned sp + -32) ->
  munch W m0 m -> wmono rsegs m0 m -> (mem_inv rsegs m0 -> mem_inv rsegs m) ->
  (ingest_refused id p len = true -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m0 m) ->
  (ingest_refused id p len = false -> rw_cells rsegs m id [CB 38 (snd (ING idb ad pb))]) ->
  r = ingest_ret id ad p len idb pb ->
  evtF rsegs RNG Post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 y8 y9 x10 x11 x12 x13 (Z_to_bv 64 r) x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x88250) fc None m (seg_rom rsegs)).
Proof.
  intros m r y5 y6 y7 y8 y9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 FR ST MU WM MI HR HN Er. subst r.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold reac_identity_ingest_post.
  do 14 eexists. exists m. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HR | exact HN].
Qed.
End TopF.

Section ArmsF.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo id ad p len : Z) (idb pb j8 : list byte) (m1 : word -> option byte) (off : Z)
  (RNG : footprint).
Hypothesis HLO : lo + 32 <= bv_unsigned sp.
Hypothesis Hid : 0 < id < 2^64.
Hypothesis Hid2 : id mod 2 = 0.
Hypothesis Had : 0 <= ad < 65536.
Hypothesis Hp : 0 <= p < 2^64.
Hypothesis Hlen : 0 <= len < 2^64.
Hypothesis Hpl : length pb = Z.to_nat len.
Hypothesis HNR : ingest_refused id p len = false.
Hypothesis RW1 : rw_cells rsegs m1 id [CB 38 idb].
Hypothesis HS4 : 0 < len -> p <> 0 -> bytes_at rsegs m1 p pb.
Hypothesis HD : 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p.
Hypothesis HDI : id + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= id.
Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra].
Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -32).
Hypothesis MU1 : munch [(bv_unsigned sp + -32, bv_unsigned sp)] m0 m1.
Hypothesis WM1 : wmono rsegs m0 m1.
Hypothesis MI1 : mem_inv rsegs m0 -> mem_inv rsegs m1.
Hypothesis HSRI : asan_shadow_rd rsegs m1 off id 38 [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)].
Hypothesis HADI : asan_addressable rsegs m1 off id 38.
Hypothesis HSRP : 0 < len -> p <> 0 ->
  asan_shadow_rd rsegs m1 off p len [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)].
Hypothesis HADP : 0 < len -> p <> 0 -> asan_addressable rsegs m1 off p len.
Hypothesis HPE : 0 < len -> p <> 0 -> p + len <= 2^47.
Hypothesis HIE : id + 38 <= 2^47.
Hypothesis Hoff : 0 <= off < 2^63.
(* the footprint premises of reac_identity_ingest_contract_F, at the shadow offset off *)
Hypothesis RFR : rng RNG (bv_unsigned sp - 32) 32.
Hypothesis RID : rng RNG id 38.
Hypothesis RIS : rng RNG (id / 8 + off) ((id + 37) / 8 - id / 8 + 1).
Hypothesis RPD : 0 < len -> p <> 0 -> rng RNG p len.
Hypothesis RPS : 0 < len -> p <> 0 -> rng RNG (p / 8 + off) ((p + len - 1) / 8 - p / 8 + 1).

Local Abbreviation W := [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)].
Local Abbreviation Post := (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0
                              lo id ad p len idb pb).
Local Abbreviation SP1 := (Z_to_bv 64 (bv_unsigned sp + -32)).
Local Abbreviation OFF := (Z_to_bv 64 off).

Definition invF (m : word -> option byte) (idb' : list byte) : Prop :=
  ivs rsegs m1 m id idb' p pb /\ rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -32).

Lemma p_nzF : 0 < len -> p <> 0.
Proof.
  intros H E. unfold ingest_refused in HNR. rewrite E in HNR.
  replace (id =? 0) with false in HNR by (symmetry; apply Z.eqb_neq; lia).
  replace (len =? 0) with false in HNR by (symmetry; apply Z.eqb_neq; lia).
  discriminate HNR.
Qed.

Lemma iv0F : 0 < len -> invF m1 idb.
Proof.
  intros H. pose proof (p_nzF H) as P0. split; [|split; [exact FR1 | exact ST1]].
  apply ivs_start; [exact RW1 | exact (HS4 H P0) |].
  rewrite Hpl, Z2Nat.id by lia. exact (HD H P0).
Qed.

Lemma idb_lenF : length idb = 38%nat.
Proof. destruct RW1 as [[[Hl _] _] _]. exact Hl. Qed.

Lemma inv_storeF : forall m idb' k bs, invF m idb' -> 0 <= k -> k + Z.of_nat (length bs) <= 38 ->
  invF (write_to_mem m (wa (id + k)) bs) (upd idb' (Z.to_nat k) bs).
Proof.
  intros m idb' k bs (IV & FR & ST) Hk Hkb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  split; [apply ivs_store; assumption|]. split.
  - apply rw_cells_frame; [exact FR | lia | lia | cbn [cells_size csize Nat.add Z.of_nat]; lia].
  - apply stk_write; [exact ST | lia | lia].
Qed.

Lemma inv_asanF : forall m idb', invF m idb' ->
  asan_shadow_rd rsegs m off id 38 W /\ asan_addressable rsegs m off id 38 /\
  (0 < len -> p <> 0 -> asan_shadow_rd rsegs m off p len W /\ asan_addressable rsegs m off p len).
Proof.
  intros m idb' (IV & _ & _). destruct (ivs_post rsegs m1 m id idb' p pb IV) as (MU & _ & _).
  assert (SUB : sub_fp [(id, id + 38)] W) by (intros x Hx; cbn [outside] in *; tauto).
  split; [exact (asan_shadow_rd_munch rsegs m1 m off id 38 W _ HSRI MU SUB)|].
  split; [exact (asan_addressable_munch rsegs m1 m off id 38 W _ HADI HSRI MU SUB)|].
  intros H1 H2. split.
  - exact (asan_shadow_rd_munch rsegs m1 m off p len W _ (HSRP H1 H2) MU SUB).
  - exact (asan_addressable_munch rsegs m1 m off p len W _ (HADP H1 H2) (HSRP H1 H2) MU SUB).
Qed.

Lemma kpF : forall m idb' i, invF m idb' -> 0 < len -> 0 <= i < len ->
  exists k : byte, ov_read_bytes rsegs m (wa ((p + i) / 8 + off)) 1 = Some [k] /\ asan_ok k (p + i).
Proof.
  intros m idb' i IV H Hi. pose proof (p_nzF H) as P0.
  destruct (inv_asanF m idb' IV) as (_ & _ & HP). destruct (HP H P0) as (SR & AD).
  destruct (asan_shadow_read rsegs m off p len W i SR Hi) as (k & RK & BK).
  exists k. split; [exact RK | exact (AD i k Hi BK)].
Qed.

Lemma kiF : forall m idb' i, invF m idb' -> 0 <= i < 38 ->
  exists k : byte, ov_read_bytes rsegs m (wa ((id + i) / 8 + off)) 1 = Some [k] /\ asan_ok k (id + i).
Proof.
  intros m idb' i IV Hi.
  destruct (inv_asanF m idb' IV) as (SR & AD & _).
  destruct (asan_shadow_read rsegs m off id 38 W i SR Hi) as (k & RK & BK).
  exists k. split; [exact RK | exact (AD i k Hi BK)].
Qed.

Lemma ki2F : forall m idb' i, invF m idb' -> 0 <= i -> i + 2 <= 38 -> (id + i) mod 8 + 2 <= 8 ->
  exists k : byte, ov_read_bytes rsegs m (wa ((id + i) / 8 + off)) 1 = Some [k] /\
                   (bv_signed k = 0 \/ (id + i) mod 8 + 1 < bv_signed k).
Proof.
  intros m idb' i IV Hi Hi2 Hm.
  destruct (inv_asanF m idb' IV) as (SR & AD & _).
  destruct (asan_shadow_read rsegs m off id 38 W i SR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|].
  pose proof (asan_check_lt rsegs m off id 38 i 2 k AD Hi ltac:(lia) Hi2 Hm BK) as OK. lia.
Qed.

Ltac inv_afterF IV k :=
  lazymatch goal with
  | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    lazymatch type of IV with
    | invF m ?idb' =>
      replace (write_to_mem m a bs) with (write_to_mem m (wa (id + k)) bs) by (f_equal; unfold wa; word_eq_tac);
      let IV' := fresh "IV" in
      pose proof (inv_storeF m idb' k bs IV ltac:(lia)
                    ltac:(rewrite ?length_le2, ?length_le1; cbn [length]; lia)) as IV';
      clear IV;
      let m' := fresh "m" in
      remember (write_to_mem m (wa (id + k)) bs) as m' eqn:Heqm; clear Heqm;
      rename IV' into IV
    end
  end.

Ltac inv_sokF IV k n :=
  lazymatch type of IV with
  | invF ?m ?idb' =>
      let SO := fresh "SO" in
      pose proof (ivs_store_ok rsegs m1 m id idb' p pb k n (proj1 IV) ltac:(lia) ltac:(lia)) as SO
  end.

Ltac inv_rdF IV i :=
  lazymatch type of IV with
  | invF ?m ?idb' =>
      let RD := fresh "RD" in
      pose proof (ivs_rdb rsegs m1 m id idb' p pb i (proj1 IV) ltac:(lia)) as RD
  end.

(* the shadow byte of a checked byte of [id, id + 37] comes from RIS, of [p, p + len - 1] from RPSa (RPS at this
   lemma's len and p), both through iiF_shadow1. *)

Lemma ret_invF : forall m idb' r (y5 y6 y7 y8 y9 x10 x11 x12 x13 x15 x17 x28 x29 x30 x31 : word),
  invF m idb' -> ING idb ad pb = (r, idb') ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 x10 x11 x12 x13 (Z_to_bv 64 r) x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x88250) fc None m (seg_rom rsegs)).
Proof.
  intros m idb' r y5 y6 y7 y8 y9 x10 x11 x12 x13 x15 x17 x28 x29 x30 x31 (IV & FR & ST) E.
  destruct (ivs_post rsegs m1 m id idb' p pb IV) as (MU & WM & MI).
  eapply ret_atF; [exact HLO | exact RFR | exact FR | exact ST | | | | | | ].
  - apply (munch_trans _ m0 m1 m).
    + eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. lia.
    + eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. tauto.
  - exact (wmono_trans rsegs m0 m1 m WM1 WM).
  - intros HI. exact (MI (MI1 HI)).
  - rewrite HNR. discriminate.
  - intros _. rewrite E. exact (ivs_rw_cells rsegs m1 m id idb' p pb IV).
  - unfold ingest_ret. rewrite HNR, E. reflexivity.
Qed.

Lemma ret0_m1F : ING idb ad pb = (0, idb) ->
  forall (y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x880a8) fc None m1 (seg_rom rsegs)).
Proof.
  intros E y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31.
  step. step.
  eapply ret_atF; [exact HLO | exact RFR | exact FR1 | exact ST1 | | exact WM1 | exact MI1 | | | ].
  - eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. lia.
  - rewrite HNR. discriminate.
  - intros _. rewrite E. exact RW1.
  - unfold ingest_ret. rewrite HNR, E. reflexivity.
Qed.

Lemma ret0_invF : forall m, invF m idb -> ING idb ad pb = (0, idb) ->
  forall (y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x880a8) fc None m (seg_rom rsegs)).
Proof.
  intros m IV E y5 y6 y7 y8 y9 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31.
  step. step. exact (ret_invF m idb 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV E).
Qed.

Lemma exit_okF : forall m idb' k (y5 y6 y7 y8 y9 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  0 <= k < 38 -> invF m idb' -> ING idb ad pb = (1, upd idb' (Z.to_nat k) [zb 1]) ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) (Z_to_bv 64 k) x12 x13 x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x88234) fc None m (seg_rom rsegs)).
Proof.
  intros m idb' k y5 y6 y7 y8 y9 x12 x13 x14 x15 x17 x28 x29 x30 x31 Hk IV E.
  clear RW1 FR1 ST1.
  destruct (kiF m idb' k IV Hk) as (kk & RK & OK).
  assert (RSk : rng RNG ((id + k) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_sokF IV k 1%nat.
  step. step. shfix. step. step. step.
  kchkF kk OK 12.
  step. step.
  inv_afterF IV k.
  eapply ret_invF; [exact IV | rewrite E, le1_lit by lia; reflexivity].
Qed.

(* 0x8815c: the four digits are checked; the shadow checks of p + 1, p, p + 2, p + 3 and of the u16 store at id,
   with the UBSan checks of p + 2, p + 3 and of the alignment of id between them. *)
Lemma fw_tailF : ad = 0 -> 4 <= len -> (forall j, (j < 4)%nat -> bz (nthb pb j) <= 9) ->
  forall (y5 y6 y7 y8 y9 x11 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) x11 (Z_to_bv 64 p) x13 x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8815c) fc None m1 (seg_rom rsegs)).
Proof.
  intros Ha H4 Hd y5 y6 y7 y8 y9 x11 x13 x14 x15 x17 x28 x29 x30 x31.
  pose proof (iv0F ltac:(lia)) as IV. clear RW1 FR1 ST1.
  assert (L4 : (4 <= length pb)%nat) by lia.
  pose proof (HPE ltac:(lia) (p_nzF ltac:(lia))) as PE.
  pose proof (RPD ltac:(lia) (p_nzF ltac:(lia))) as RPa.
  pose proof (RPS ltac:(lia) (p_nzF ltac:(lia))) as RPSa.
  step. step. step.
  rewrite ii_ltu_lit by lia.
  replace (p + 2 <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  destruct (kpF m1 idb 1 IV ltac:(lia) ltac:(lia)) as (k1 & RK & OK1).
  assert (RSp1 : rng RNG ((p + 1) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. step. shfix. step. step. clear RK. step.
  kchkF k1 OK1 15.
  destruct (kpF m1 idb 0 IV ltac:(lia) ltac:(lia)) as (k0 & RK & OK0). rewrite !Z.add_0_r in RK, OK0.
  assert (RSp0 : rng RNG (p / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  inv_rdF IV 1%nat.
  step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k0 OK0 15.
  destruct (kpF m1 idb 2 IV ltac:(lia) ltac:(lia)) as (k2 & RK & OK2).
  assert (RSp2 : rng RNG ((p + 2) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  inv_rdF IV 0%nat.
  step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k2 OK2 17.
  step. step.
  rewrite ii_ltu_neg_lit by lia.
  replace (-4 + 2^64 <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step.
  rewrite ii_land1 by lia.
  replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb].
  destruct (kpF m1 idb 3 IV ltac:(lia) ltac:(lia)) as (k3 & RK & OK3).
  assert (RSp3 : rng RNG ((p + 3) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  inv_rdF IV 2%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k3 OK3 17.
  destruct (ki2F m1 idb 0 IV ltac:(lia) ltac:(lia) ltac:(lia)) as (ki0 & RK & OKI).
  rewrite !Z.add_0_r in RK, OKI.
  assert (RSi0 : rng RNG (id / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_rdF IV 3%nat.
  step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF ki0 OKI 17.
  inv_sokF IV 0 2%nat.
  do 10 step.
  inv_afterF IV 0.
  step. step.
  eapply exit_okF; [lia | exact IV |].
  assert (D0 : bz (nthb pb 0) <= 9) by (apply Hd; lia).
  assert (D1 : bz (nthb pb 1) <= 9) by (apply Hd; lia).
  assert (D2 : bz (nthb pb 2) <= 9) by (apply Hd; lia).
  assert (D3 : bz (nthb pb 3) <= 9) by (apply Hd; lia).
  rewrite Ha, (ING_fw idb pb L4).
  rewrite (proj2 (Z.leb_le _ _) D0), (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_le _ _) D2),
    (proj2 (Z.leb_le _ _) D3).
  cbn [andb]. rewrite !zxb_u.
  unfold bz, nthb, zb in *.
  pose proof (byte_range (nth 0 pb (Z_to_bv 8 0))). pose proof (byte_range (nth 1 pb (Z_to_bv 8 0))).
  pose proof (byte_range (nth 2 pb (Z_to_bv 8 0))). pose proof (byte_range (nth 3 pb (Z_to_bv 8 0))).
  rewrite le2_le16 by lia.
  match goal with
  | |- (_, upd (upd _ _ (le16 ?a)) _ _) = (_, upd (upd _ _ (le16 ?b)) _ _) =>
      replace a with b by (unfold fw_value, bz, nthb, zb; lia)
  end.
  reflexivity.
Qed.

(* 0x87e64: the digit loop; a1 = a7 = p + i, a4 = the bytes left, a3 = (p <> 0), a5 = 9. *)
Lemma fw_loopF : ad = 0 -> 4 <= len -> forall n i (a1w a7w y5 y6 y7 y8 y9 x28 x29 x30 x31 : word),
  a1w = Z_to_bv 64 (p + Z.of_nat i) -> a7w = Z_to_bv 64 (p + Z.of_nat i) ->
  (i + n = 4)%nat -> (0 < n)%nat -> (forall j, (j < i)%nat -> bz (nthb pb j) <= 9) ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) a1w (Z_to_bv 64 p) (Z_to_bv 64 1)
             (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 9) OFF a7w s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x87e64) fc None m1 (seg_rom rsegs)).
Proof.
  intros Ha H4 n. induction n as [|n IH];
    intros i a1w a7w y5 y6 y7 y8 y9 x28 x29 x30 x31 E1 E7 Hin Hn Hd; [lia|].
  subst a1w a7w.
  pose proof (iv0F ltac:(lia)) as IV.
  assert (L4 : (4 <= length pb)%nat) by lia.
  pose proof (p_nzF ltac:(lia)) as P0.
  pose proof (HPE ltac:(lia) P0) as PE.
  pose proof (RPD ltac:(lia) P0) as RPa.
  pose proof (RPS ltac:(lia) P0) as RPSa.
  step. rewrite ii_ltu_lit by lia.
  replace (p + Z.of_nat i <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. rewrite ii_seqz by lia.
  step. step. if_false.
  step. rewrite ii_eqb_lit by lia.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  inv_rdF IV i.
  destruct (kpF m1 idb (Z.of_nat i) IV ltac:(lia) ltac:(lia)) as (k & RK & OK).
  assert (RSpi : rng RNG ((p + Z.of_nat i) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  pose proof (byte_range (nth i pb (Z_to_bv 8 0))) as BR.
  step. shfix. step. step. step.
  kchkF k OK 6.
  step. step.
  rewrite ii_ltu_zxb by lia.
  destruct (Z.ltb_spec 9 (bv_unsigned (nth i pb (Z_to_bv 8 0)))) as [Hb|Hb]; cbv iota.
  - eapply ret0_m1F. rewrite Ha. apply (fw_bad idb pb i L4); [lia|]. exact Hb.
  - step. step. step. step.
    replace (Z.of_nat (S n) + -1) with (Z.of_nat n) by lia.
    rewrite ii_eqb_lit by lia.
    destruct n as [|n].
    + replace (Z.of_nat 0 =? 0) with true by reflexivity. cbv iota.
      replace i with 3%nat in * by lia.
      apply (fw_tailF Ha H4).
      intros j Hj. destruct (Nat.eq_dec j 3) as [->|Hj3]; [unfold bz, nthb, zb in *; lia | apply Hd; lia].
    + replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      apply (IH (S i)); [f_equal; lia | f_equal; lia | lia | lia |].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [unfold bz, nthb, zb in *; lia | apply Hd; lia].
Qed.

(* 0x87eb4: the version record. The asan image's code with the UBSan checks of the alignment of id and of
   p + 2, p + 4, p + 6 (each before the bytes are read) between the shadow checks. *)
Lemma ver_armF : ad = 1536 ->
  forall (y5 y6 y7 y8 y9 x11 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) x11 (Z_to_bv 64 p) (Z_to_bv 64 len) x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x87eb4) fc None m1 (seg_rom rsegs)).
Proof.
  intros Ha y5 y6 y7 y8 y9 x11 x14 x15 x17 x28 x29 x30 x31.
  step. step.
  rewrite ii_ltu_lit by lia.
  destruct (Z.ltb_spec len 8) as [H8|H8]; cbv iota.
  { eapply ret0_m1F. rewrite Ha. apply ING_ver_short. lia. }
  pose proof idb_lenF as LI.
  pose proof (iv0F ltac:(lia)) as IV. clear RW1 FR1 ST1.
  assert (L8 : (8 <= length pb)%nat) by lia.
  pose proof (HPE ltac:(lia) (p_nzF ltac:(lia))) as PE.
  pose proof (RPD ltac:(lia) (p_nzF ltac:(lia))) as RPa.
  pose proof (RPS ltac:(lia) (p_nzF ltac:(lia))) as RPSa.
  step. step.
  rewrite ii_land1 by lia.
  replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb].
  destruct (kpF m1 idb 0 IV ltac:(lia) ltac:(lia)) as (kp0 & RK & OKp0). rewrite !Z.add_0_r in RK, OKp0.
  assert (RSp0 : rng RNG (p / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. shfix. step. step. clear RK. step.
  kchkF kp0 OKp0 13.
  destruct (kpF m1 idb 7 IV ltac:(lia) ltac:(lia)) as (kp7 & RK & OKp7).
  assert (RSp7 : rng RNG ((p + 7) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. step. shfix. step. step. clear RK. step.
  kchkF kp7 OKp7 14.
  destruct (kiF m1 idb 28 IV ltac:(lia)) as (k28 & RK & OK28).
  assert (RSi28 : rng RNG ((id + 28) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_rdF IV 0%nat. inv_rdF IV 1%nat. inv_rdF IV 2%nat. inv_rdF IV 3%nat.
  do 6 step. shfix. step. step. clear RK.
  clear RD RD0 RD1 RD2.
  inv_rdF IV 4%nat. inv_rdF IV 5%nat. inv_rdF IV 6%nat. inv_rdF IV 7%nat.
  do 4 step. clear RD RD0 RD1 RD2.
  step.
  kchkF k28 OK28 8.
  destruct (kiF m1 idb 35 IV ltac:(lia)) as (k35 & RK & OK35).
  assert (RSi35 : rng RNG ((id + 35) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  step. step. shfix. step. step. clear RK. step.
  kchkF k35 OK35 9.
  do 18 step.
  vsum_regF pb 11.
  pose proof (vsum_range pb) as VR.
  rewrite (unsigned_lit (vsum pb)) by lia. rewrite ?ii_shr16, ?ii_shr32, ?ii_shr48.
  inv_sokF IV 28 2%nat. step. rewrite vs0. inv_afterF IV 28.
  inv_sokF IV 30 2%nat. step. rewrite vs1. inv_afterF IV 30.
  inv_sokF IV 32 2%nat. step. rewrite vs2. inv_afterF IV 32.
  inv_sokF IV 34 2%nat. step. rewrite vs3. inv_afterF IV 34.
  step.
  rewrite b_ltu_neg_rF by lia.
  replace (p <? -2 + 2^64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  step. step. step.
  rewrite ii_eqb_neg_lit by lia.
  replace (p + 2 =? -1 + 2^64) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  destruct (kpF _ _ 2 IV ltac:(lia) ltac:(lia)) as (kp2 & RK & OKp2).
  assert (RSp2 : rng RNG ((p + 2) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. shfix. step. step. clear RK. step.
  kchkF kp2 OKp2 15.
  destruct (kpF _ _ 3 IV ltac:(lia) ltac:(lia)) as (kp3 & RK & OKp3).
  assert (RSp3 : rng RNG ((p + 3) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  inv_rdF IV 2%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF kp3 OKp3 11.
  destruct (ki2F _ _ 22 IV ltac:(lia) ltac:(lia) ltac:(lia)) as (k22 & RK & OK22).
  assert (RSi22 : rng RNG ((id + 22) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_rdF IV 3%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k22 OK22 6.
  inv_sokF IV 22 2%nat. do 4 step. rewrite le2_orshl. inv_afterF IV 22.
  step.
  rewrite ii_ltu_neg_lit by lia.
  replace (-5 + 2^64 <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. step.
  rewrite ii_eqb_neg_lit by lia.
  replace (p + 4 =? -1 + 2^64) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  destruct (kpF _ _ 4 IV ltac:(lia) ltac:(lia)) as (kp4 & RK & OKp4).
  assert (RSp4 : rng RNG ((p + 4) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. shfix. step. step. clear RK. step.
  kchkF kp4 OKp4 15.
  destruct (kpF _ _ 5 IV ltac:(lia) ltac:(lia)) as (kp5 & RK & OKp5).
  assert (RSp5 : rng RNG ((p + 5) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  inv_rdF IV 4%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF kp5 OKp5 11.
  destruct (ki2F _ _ 24 IV ltac:(lia) ltac:(lia) ltac:(lia)) as (k24 & RK & OK24).
  assert (RSi24 : rng RNG ((id + 24) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_rdF IV 5%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k24 OK24 6.
  inv_sokF IV 24 2%nat. do 4 step. rewrite le2_orshl. inv_afterF IV 24.
  step.
  rewrite ii_ltu_neg_lit by lia.
  replace (-7 + 2^64 <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. step.
  rewrite ii_eqb_neg_lit by lia.
  replace (p + 6 =? -1 + 2^64) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  destruct (kpF _ _ 6 IV ltac:(lia) ltac:(lia)) as (kp6 & RK & OKp6).
  assert (RSp6 : rng RNG ((p + 6) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. shfix. step. step. clear RK. step.
  kchkF kp6 OKp6 14.
  destruct (kpF _ _ 7 IV ltac:(lia) ltac:(lia)) as (kp7' & RK & OKp7').
  inv_rdF IV 6%nat.
  step. clear RK. step. clear RD. step.
  kchkF kp7' OKp7' 14.
  destruct (ki2F _ _ 26 IV ltac:(lia) ltac:(lia) ltac:(lia)) as (k26 & RK & OK26).
  assert (RSi26 : rng RNG ((id + 26) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_rdF IV 7%nat.
  step. step. shfix. step. step. clear RK. step. clear RD. step.
  kchkF k26 OK26 15.
  inv_sokF IV 26 2%nat. do 3 step. rewrite le2_orshl. inv_afterF IV 26.
  step. step.
  eapply exit_okF; [lia | exact IV |].
  rewrite Ha, (ING_ver idb pb L8).
  rewrite (ver_eq idb) by exact LI. reflexivity.
Qed.

Local Abbreviation NN := (Nat.min (length pb - 1) 16).

(* 0x88214: the name's end: the UBSan check of id + 3 + w, the shadow check of the 0 byte at id + 3 + w, the 0
   byte; then has_model_name at 0x88234. *)
Lemma name_tailF : ad = 4096 -> 2 <= len -> forall w m (y5 y6 y7 y8 y9 x11 x12 x15 x28 x29 x30 x31 : word),
  (1 <= w)%nat -> name_len pb = w ->
  invF m (upd idb 3 (firstn w (skipn 1 pb))) ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) x11 x12 (Z_to_bv 64 (Z.of_nat w)) (Z_to_bv 64 (id + 3))
             x15 OFF (Z_to_bv 64 (18446744073709551615 - (id + 3))) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x88214) fc None m (seg_rom rsegs)).
Proof.
  intros Ha H2 w m y5 y6 y7 y8 y9 x11 x12 x15 x28 x29 x30 x31 Hw NL IV.
  pose proof idb_lenF as LI. clear RW1 FR1 ST1.
  pose proof (name_len_le pb) as NLE.
  step.
  rewrite ii_ltu_lit by lia.
  replace (18446744073709551615 - (id + 3) <? Z.of_nat w) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  destruct (kiF m _ (3 + Z.of_nat w) IV ltac:(lia)) as (kc & RK & OKc).
  assert (RSc : rng RNG ((id + (3 + Z.of_nat w)) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
  inv_sokF IV (3 + Z.of_nat w) 1%nat.
  step. step. shfix. step. step. clear RK. step.
  kchkF kc OKc 13.
  step.
  inv_afterF IV (3 + Z.of_nat w).
  step.
  eapply exit_okF; [lia | exact IV |].
  rewrite Ha, (ING_name idb pb) by lia. rewrite NL.
  rewrite !le1_lit by lia.
  rewrite (upd_cat idb (firstn w (skipn 1 pb)) [zb 0] 3 (Z.to_nat (3 + Z.of_nat w)))
    by (rewrite ?length_firstn, ?length_skipn; lia).
  reflexivity.
Qed.

(* 0x880dc: the name loop; a3 = i, t1 = p + 1, a4 = id + 3, a7 = ~(id + 3), t0 = id & 1 = 0, t2 = -1, a5 = NN. *)
Lemma name_loopF : ad = 4096 -> 2 <= len -> forall k i m (a3w y8 y9 x11 x28 x29 x30 x31 : word),
  a3w = Z_to_bv 64 (Z.of_nat i) ->
  (i + k = NN)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> bz (nthb pb (1 + j)) <> 0) ->
  invF m (upd idb 3 (firstn i (skipn 1 pb))) ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp (Z_to_bv 64 0) (Z_to_bv 64 (p + 1)) (Z_to_bv 64 (-1)) y8 y9 (Z_to_bv 64 id) x11
             (Z_to_bv 64 p) a3w (Z_to_bv 64 (id + 3)) (Z_to_bv 64 (Z.of_nat NN)) OFF
             (Z_to_bv 64 (18446744073709551615 - (id + 3))) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x880dc) fc None m (seg_rom rsegs)).
Proof.
  intros Ha H2 k. induction k as [|k IH]; intros i m a3w y8 y9 x11 x28 x29 x30 x31 E3 Hik Hk Hnz IV; [lia|].
  subst a3w.
  pose proof idb_lenF as LI.
  pose proof (p_nzF ltac:(lia)) as P0.
  pose proof (HPE ltac:(lia) P0) as PE.
  pose proof (RPD ltac:(lia) P0) as RPa.
  pose proof (RPS ltac:(lia) P0) as RPSa.
  step. step.
  rewrite ii_xor_ne1 by lia. cbv iota.
  destruct (kpF m _ (1 + Z.of_nat i) IV ltac:(lia) ltac:(lia)) as (ka & RK & OKa).
  replace (p + (1 + Z.of_nat i)) with (p + 1 + Z.of_nat i) in RK, OKa by lia.
  assert (RSa : rng RNG ((p + 1 + Z.of_nat i) / 8 + off) 1) by (eapply iiF_shadow1; [exact RPSa | lia]).
  step. step. shfix. step. step. clear RK. step.
  kchkF ka OKa 29.
  inv_rdF IV (1 + i)%nat.
  replace (p + Z.of_nat (1 + i)) with (p + 1 + Z.of_nat i) in RD by lia.
  step. clear RD.
  step.
  rewrite ii_eqb_zxb0.
  destruct (Z.eqb_spec (bv_unsigned (nth (1 + i) pb (Z_to_bv 8 0))) 0) as [Hz|Hz]; cbv iota.
  - step. rewrite ii_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat i) 0) as [I0|I0]; cbv iota.
    + assert (i = 0%nat) by lia. subst i.
      cbn [firstn] in IV. rewrite upd_nil in IV by lia.
      eapply ret0_invF; [exact IV|].
      rewrite Ha, ING_name_zero; [reflexivity|].
      right. apply name_len_hit; [lia | lia | exact Hz | intros j Hj; lia].
    + step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb].
      step. step.
      rewrite ii_ltu_lit by lia.
      replace (16 <? Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
      eapply name_tailF; [exact Ha | exact H2 | lia | | exact IV].
      apply name_len_hit; [lia | lia | exact Hz | exact Hnz].
  - step.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb].
    step.
    rewrite ii_ltu_lit by lia.
    replace (18446744073709551615 - (id + 3) <? Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    destruct (kiF m _ (3 + Z.of_nat i) IV ltac:(lia)) as (kb & RK & OKb).
    replace (id + (3 + Z.of_nat i)) with (id + 3 + Z.of_nat i) in RK, OKb by lia.
    assert (RSb : rng RNG ((id + 3 + Z.of_nat i) / 8 + off) 1) by (eapply iiF_shadow1; [exact RIS | lia]).
    step. step. shfix. step. step. clear RK. step.
    kchkF kb OKb 30.
    inv_sokF IV (3 + Z.of_nat i) 1%nat.
    step. step.
    inv_afterF IV (3 + Z.of_nat i).
    rewrite le1_zxb in IV.
    rewrite (upd_cat idb (firstn i (skipn 1 pb)) [nth (1 + i) pb (Z_to_bv 8 0)] 3 (Z.to_nat (3 + Z.of_nat i)))
      in IV by (rewrite ?length_firstn, ?length_skipn; lia).
    replace (firstn i (skipn 1 pb) ++ [nth (1 + i) pb (Z_to_bv 8 0)]) with (firstn (S i) (skipn 1 pb)) in IV
      by (rewrite firstn_snoc by (rewrite length_skipn; lia); rewrite nthb_skipn1; reflexivity).
    assert (Hnz' : forall j, (j < S i)%nat -> bz (nthb pb (1 + j)) <> 0).
    { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hz | apply Hnz; lia]. }
    step.
    rewrite ii_eqb_lit by lia.
    destruct k as [|k].
    + replace (Z.of_nat NN =? Z.of_nat i + 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step. step.
      replace (S i) with NN in IV by lia.
      eapply name_tailF; [exact Ha | exact H2 | lia | | exact IV].
      apply name_len_full; [lia | intros j Hj; apply Hnz'; lia].
    + replace (Z.of_nat NN =? Z.of_nat i + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      cbv iota.
      apply (IH (S i)); [f_equal; lia | lia | lia | exact Hnz' | exact IV].
Qed.

(* 0x880c0: the UBSan check of a null p, then the loop's registers. *)
Lemma name_preF : ad = 4096 -> 2 <= len -> forall (a5w y5 y6 y7 y8 y9 x11 x13 x14 x17 x28 x29 x30 x31 : word),
  a5w = Z_to_bv 64 (Z.of_nat NN) ->
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) x11 (Z_to_bv 64 p) x13 x14 a5w OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x880c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros Ha H2 a5w y5 y6 y7 y8 y9 x11 x13 x14 x17 x28 x29 x30 x31 E5. subst a5w.
  pose proof idb_lenF as LI.
  pose proof (iv0F ltac:(lia)) as IV.
  pose proof (p_nzF ltac:(lia)) as P0.
  step.
  rewrite ii_eqb_lit by lia.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 6 step.
  rewrite ii_land1 by lia.
  rewrite (unsigned_lit (id + 3)) by lia. rewrite zb_lxor_ones by lia.
  apply (name_loopF Ha H2 NN 0 m1); [reflexivity | lia | lia | intros j Hj; lia |].
  cbn [firstn]. rewrite upd_nil by lia. exact IV.
Qed.

Lemma name_armF : ad = 4096 ->
  forall (y5 y6 y7 y8 y9 x11 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) x11 (Z_to_bv 64 p) (Z_to_bv 64 len) x14 x15 OFF x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x880a0) fc None m1 (seg_rom rsegs)).
Proof.
  intros Ha y5 y6 y7 y8 y9 x11 x14 x15 x17 x28 x29 x30 x31.
  step. step.
  rewrite ii_ltu_lit by lia.
  destruct (Z.ltb_spec len 2) as [H2|H2]; cbn [negb]; cbv iota.
  - eapply ret0_m1F. rewrite Ha. apply ING_name_zero. left. lia.
  - step. step. step.
    rewrite ii_ltu_lit by lia.
    destruct (Z.ltb_spec (len + -1) 16) as [H16|H16]; cbv iota.
    + apply (name_preF Ha H2). f_equal. lia.
    + step. apply (name_preF Ha H2). f_equal. lia.
Qed.

Lemma dispatchF : forall (y5 y6 y7 y8 y9 x14 x15 x17 x28 x29 x30 x31 : word),
  evtF rsegs RNG Post
    (MS (mkR ra SP1 gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 id) (Z_to_bv 64 ad) (Z_to_bv 64 p) (Z_to_bv 64 len)
             x14 x15 OFF x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x87e38) fc None m1 (seg_rom rsegs)).
Proof.
  intros y5 y6 y7 y8 y9 x14 x15 x17 x28 x29 x30 x31.
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 4096) as [A1|A1]; cbv iota; [exact (name_armF A1 _ _ _ _ _ _ _ _ _ _ _ _ _)|].
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 1536) as [A2|A2]; cbv iota; [exact (ver_armF A2 _ _ _ _ _ _ _ _ _ _ _ _ _)|].
  step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 0) as [A3|A3]; cbn [negb]; cbv iota.
  - step. step.
    rewrite ii_ltu_lit by lia.
    destruct (Z.ltb_spec len 4) as [H4|H4]; cbv iota.
    + eapply ret0_m1F. rewrite A3. apply ING_fw_short. lia.
    + pose proof (p_nzF ltac:(lia)) as P0.
      step. rewrite ii_snez by lia.
      step. step. step.
      change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat 4)).
      apply (fw_loopF A3 H4 4 0); [f_equal; lia | f_equal; lia | lia | lia | intros j Hj; lia].
  - eapply ret0_m1F. apply ING_other; assumption.
Qed.

End ArmsF.

Theorem reac_identity_ingest_F_holds_on : reac_identity_ingest_contract_F_on.
Proof.
  unfold reac_identity_ingest_contract_F_on, reac_identity_ingest_W, REAC_IDENTITY_INGEST,
    REAC_IDENTITY_INGEST_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo id ad p len idb pb -> -> -> -> Hid Had Hp Hlen HS3 Hpl HS4 HD ST HLO HDI HDP HCE HADI HADP HW
    RFR RGK RCK RIDS RPDS.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  (* the two runtime cells are read at literal addresses: keep unfolded copies of their rng premises *)
  pose proof RGK as RGz. unfold GOT_CELL_K in RGz.
  pose proof RCK as RCz. unfold CELL_K in RCz.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 32 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; exact (rc_wv_stk rsegs m _ _ x ST ltac:(lia))).
  carve_frame 32%nat ST.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (MI1 : mem_inv rsegs m -> mem_inv rsegs m1)
    by (intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)).
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec id 0) as [I0|I0]; cbv iota.
  - eapply ret_atF; [exact HLO | exact RFR | eassumption | eassumption | | eassumption | exact MI1 | | | ].
    + eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    + intros _. eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    + unfold ingest_refused. rewrite I0. cbn. discriminate.
    + unfold ingest_ret, ingest_refused. rewrite I0. reflexivity.
  - destruct (HS3 I0) as (Hid2 & RW0). specialize (HDI I0). specialize (HADI I0).
    destruct (RIDS I0) as (RID & RIS).
    assert (RPDa : 0 < len -> p <> 0 -> rng RNG p len) by (intros H1 H2; exact (proj1 (RPDS H1 H2))).
    assert (RPSa : 0 < len -> p <> 0 ->
              rng RNG (p / 8 + ASAN_K) ((p + len - 1) / 8 - p / 8 + 1))
      by (intros H1 H2; exact (proj2 (RPDS H1 H2))).
    clear RIDS RPDS.
    pose proof (rt_addressable_bound m id 38 HADI) as HIE.
    assert (SUB : sub_fp [(bv_unsigned sp + -32, bv_unsigned sp)]
                    [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)])
      by (intros x Hx; cbn [outside] in *; lia).
    pose proof (rt_shadow_rd m id 38 _ HADI (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSRI.
    pose proof (rt_addressable m id 38 HADI) as HADI'.
    assert (HSRP : 0 < len -> p <> 0 ->
              asan_shadow_rd rsegs m ASAN_K p len [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)])
      by (intros H1 H2; exact (rt_shadow_rd m p len _ (HADP H1 H2) (fun x Hx => HW x (or_intror (or_intror Hx))))).
    assert (HADP' : 0 < len -> p <> 0 -> asan_addressable rsegs m ASAN_K p len)
      by (intros H1 H2; exact (rt_addressable m p len (HADP H1 H2))).
    assert (HPE : 0 < len -> p <> 0 -> p + len <= 2^47)
      by (intros H1 H2; pose proof (rt_addressable_bound m p len (HADP H1 H2)); lia).
    pose proof (asan_rt_munch rsegs m m1 _ _ _ _ _ HRT MU SUB) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 _ id 38 _ _ HSRI MU SUB) as HSRI1.
    pose proof (asan_addressable_munch rsegs m m1 _ id 38 _ _ HADI' HSRI MU SUB) as HADI1.
    assert (HSRP1 : 0 < len -> p <> 0 ->
              asan_shadow_rd rsegs m1 ASAN_K p len [(bv_unsigned sp - 32, bv_unsigned sp); (id, id + 38)])
      by (intros H1 H2; exact (asan_shadow_rd_munch rsegs m m1 _ p len _ _ (HSRP H1 H2) MU SUB)).
    assert (HADP1 : 0 < len -> p <> 0 -> asan_addressable rsegs m1 ASAN_K p len)
      by (intros H1 H2; exact (asan_addressable_munch rsegs m m1 _ p len _ _ (HADP' H1 H2) (HSRP H1 H2) MU SUB)).
    assert (RW1 : rw_cells rsegs m1 id [CB 38 idb])
      by (apply (rw_cells_transport rsegs _ m m1 id _ RW0 MU WM); cbn [disjoint_from cells_size csize Z.of_nat];
          lia).
    assert (HS41 : 0 < len -> p <> 0 -> bytes_at rsegs m1 p pb)
      by (intros H1 H2; apply (bytes_at_transport rsegs _ m m1 p pb (HS4 H1 H2) MU);
          cbn [disjoint_from]; rewrite Hpl, Z2Nat.id by lia; specialize (HDP H1 H2); lia).
    pose proof (asan_rt_got_read rsegs m1 _ _ _ _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ _ _ HRT1) as RC.
    assert (Hoff : 0 <= ASAN_K < 2^63) by (unfold ASAN_K; lia).
    set (off := ASAN_K) in RC, HSRI1, HADI1, HSRP1, HADP1, Hoff, RIS, RPSa. clearbody off.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    clear HRT HRT1 HSRI HADI' HSRP HADP' HS3 HS4 HADI HADP HW HCE RW0.
    step. step. step. clear RG RC.
    step.
    rewrite ii_eqb_lit by lia.
    destruct (Z.eqb_spec p 0) as [P0|P0]; cbn [negb]; cbv iota.
    + step.
      rewrite ii_eqb_lit by lia.
      destruct (Z.eqb_spec len 0) as [L0|L0]; cbn [negb]; cbv iota.
      * assert (HNR : ingest_refused id p len = false).
        { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq id 0) I0), L0. reflexivity. }
        eapply dispatchF; try eassumption; try lia.
        all: intros x Hx; cbn [outside] in *; lia.
      * eapply ret_atF; [exact HLO | exact RFR | eassumption | eassumption | | eassumption | exact MI1 | | | ].
        -- eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
        -- intros _. eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
        -- unfold ingest_refused. rewrite P0, (proj2 (Z.eqb_neq len 0) L0), Bool.orb_true_r. discriminate.
        -- unfold ingest_ret, ingest_refused. rewrite P0, (proj2 (Z.eqb_neq len 0) L0), Bool.orb_true_r.
           reflexivity.
    + assert (HNR : ingest_refused id p len = false).
      { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq id 0) I0), (proj2 (Z.eqb_neq p 0) P0).
        rewrite Bool.andb_false_r. reflexivity. }
      eapply dispatchF; try eassumption; try lia.
      all: intros x Hx; cbn [outside] in *; lia.
Qed.

(* The old footprint statement, one line from the _on one (route (C): shadow_rw dropped, not needed). *)
Theorem reac_identity_ingest_F_holds : reac_identity_ingest_contract_F.
Proof. exact (reac_identity_ingest_contract_F_of_F_on reac_identity_ingest_F_holds_on). Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. *)
Theorem reac_identity_ingest_holds_of_F : reac_identity_ingest_contract.
Proof. exact (reac_identity_ingest_contract_of_F reac_identity_ingest_F_holds). Qed.
