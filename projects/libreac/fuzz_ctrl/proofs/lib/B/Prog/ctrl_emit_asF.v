(* The footprint twin of ctrl_emit_as.v (image B, asan-ubsan build; RECIPE.md step 1 (a working note, not in this delivery)): the same run as
   an ExecF.evtF under a footprint RNG (ctrl_emit_as_contract_F of lib/B/Prog/ctrl_emit_as_c.v), by the script of
   ctrl_emit_as.v over StepF's step. Each access of this image's own code is closed from one rng premise: the frame
   stores and loads in the window [LO, SP0); the two 8-byte loads of the GOT cell and the runtime cell (both in the
   image [0x10000, 0x5fe000)); the 1-byte loads of the row bytes f, f + 1, f + 21 .. f + 23 and the 4-byte load of
   md + 56 and the 1-byte load of each one's shadow byte; the 1-byte stores of the six header bytes o + 12 .. o + 17
   and the two trailer bytes o + LEN - 2, o + LEN - 1 and their shadow bytes.  The run has five callees:
   __asan_memset (the output zero-fill), the two __asan_memcpy copies (d, s into the output), ctrl_lay_block and
   reac_braid_encode; ctrl_emit_as.v's theorem takes each callee's old contract as a hypothesis, so this twin takes
   its footprint form in the same place.  ctrl_finish_contract_F (ctrl_finish_c.v), ctrl_lay_block_contract_F
   (ctrl_lay_block_c.v, the ctrl_lay_block lane's published text) and reac_braid_encode_ns0_contract_F
   (reac_braid_encode_ns0_c.v, this unit's reac_braid_encode lane) are imported.  The other two _F statements had
   no clean home in this worktree then, so they were stated here in their owners' canonical shape (old contract + one
   rng premise per region the callee touches) with the owner named: __asan_memset / __asan_memcpy belong to
   a Theorem Labs lane (text of lib/B/Prog/reac_identity_initF.v, declaration_ofF.v); now Required from asan_memset_cF.v / asan_memcpy_cF.v (:30).
   ctrl_emit_as_contract_of_F (lib/B/Prog/ctrl_emit_as_c.v) re-derives the old contract from this footprint form.
   ctrl_emit_as.v and its theorem are unchanged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcFinLib RcEmit RcEmitLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  asan_memcpy_c asan_memset_c ctrl_lay_block_c reac_braid_encode_ns0_c ctrl_finish_c reac_box_model_block_c
  ctrl_emit_as_c.
(* E4 of the glue draft: the ONE text of record of the two runtime helpers (a Theorem Labs lane, 9869f1d1f86); this file
   used to carry its own copy of each. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_cF asan_memcpy_cF.
(* Route (C) (a Theorem Labs lane, the _on block at the end of Section Emit): the leaf region predicate (lib/B/ShadowRwOn.v),
   the shadow-word region (lib/B/Prog/sh_word_on.v) and a Theorem Labs lane's _on statements of the two runtime helpers.  No
   name these files define occurs in the text above the _on block, so this Import changes the meaning of no old
   line.  ShadowRwOnT.v is NOT Required: see ae_fl_shadow_rw_on below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import sh_word_on asan_memset_c_on asan_memset_cF_on
  asan_memcpy_c_on asan_memcpy_cF_on.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes StepF.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* asan_memset_contract_F and asan_memcpy_contract_F are a Theorem Labs lane's texts of record, in lib/B/Prog/asan_memset_cF.v
   and lib/B/Prog/asan_memcpy_cF.v (Required above).  Against the copies this file used to carry, they ask for
   three more footprint premises at each call: `rng_bytes RNG`, the whole image `rng RNG IMG_LO (IMG_HI - IMG_LO)`
   (which covers the runtime words, so the old RT_LO/RT_HI premise is gone), and the 8-aligned shadow word span of
   the helper's own stack window.  The three call sites below discharge them from FpRB, FpIMG and FpWSH. *)

(* ------------------------------------------------------------------------------------------------------------ *)
(* The 8-aligned shadow word cover of [a, b] is monotone in its ends (the dcF lemmas of declaration_ofF.v): it
   covers the cover of a sub-range and the single shadow byte and the byte-exact span of any sub-range. The three
   shcov wrappers take the statement's rng_shcov premise directly. All are proved in a context with no other
   division,
   so the run's step goals never add Euclidean equations. *)
Lemma dcF_alig_mono : forall K a a', a <= a' -> (a / 8 + K) / 8 * 8 <= (a' / 8 + K) / 8 * 8.
Proof. intros K a a' H. Z.div_mod_to_equations. lia. Qed.

Lemma dcF_shadowcov : forall RNG K a b a' b',
  rng RNG ((a / 8 + K) / 8 * 8) ((b / 8 + K) / 8 * 8 + 8 - (a / 8 + K) / 8 * 8) ->
  a <= a' -> a' <= b' -> b' <= b ->
  rng RNG ((a' / 8 + K) / 8 * 8) ((b' / 8 + K) / 8 * 8 + 8 - (a' / 8 + K) / 8 * 8).
Proof.
  intros RNG K a b a' b' H H1 H2 H3.
  pose proof (dcF_alig_mono K a a' H1). pose proof (dcF_alig_mono K b' b H3).
  eapply rng_sub; [exact H | lia | lia].
Qed.

Lemma dcF_shadow1 : forall RNG K a b x,
  rng RNG ((a / 8 + K) / 8 * 8) ((b / 8 + K) / 8 * 8 + 8 - (a / 8 + K) / 8 * 8) ->
  a <= x <= b -> rng RNG (x / 8 + K) 1.
Proof.
  intros RNG K a b x H Hx.
  assert (L1 : a / 8 <= x / 8) by (Z.div_mod_to_equations; lia).
  assert (L2 : x / 8 <= b / 8) by (Z.div_mod_to_equations; lia).
  eapply rng_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

Lemma dcF_shadowspan : forall RNG K a b a' b',
  rng RNG ((a / 8 + K) / 8 * 8) ((b / 8 + K) / 8 * 8 + 8 - (a / 8 + K) / 8 * 8) ->
  a <= a' -> a' <= b' -> b' <= b -> rng RNG (a' / 8 + K) (b' / 8 - a' / 8 + 1).
Proof.
  intros RNG K a b a' b' H H1 H2 H3.
  assert (La : a / 8 <= a' / 8) by (Z.div_mod_to_equations; lia).
  assert (Lb : b' / 8 <= b / 8) by (Z.div_mod_to_equations; lia).
  eapply rng_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

(* The three consequences a run draws from one aligned-cover premise rng_shcov RNG p n (= the cover of [p, p+n-1]):
   the aligned cover of a sub-range, the byte-exact span of a sub-range, and one shadow byte. *)
Lemma shcov_sub : forall RNG p n a b, rng_shcov RNG p n -> p <= a -> a <= b -> b <= p + n - 1 ->
  rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
Proof.
  intros RNG p n a b H Ha Hab Hb. unfold rng_shcov, shadow_addr in H.
  exact (dcF_shadowcov RNG ASAN_K p (p + n - 1) a b H Ha Hab Hb).
Qed.

Lemma shcov_span : forall RNG p n a b, rng_shcov RNG p n -> p <= a -> a <= b -> b <= p + n - 1 ->
  rng RNG (a / 8 + ASAN_K) (b / 8 - a / 8 + 1).
Proof.
  intros RNG p n a b H Ha Hab Hb. unfold rng_shcov, shadow_addr in H.
  exact (dcF_shadowspan RNG ASAN_K p (p + n - 1) a b H Ha Hab Hb).
Qed.

Lemma shcov_byte : forall RNG p n x, rng_shcov RNG p n -> p <= x <= p + n - 1 -> rng RNG (x / 8 + ASAN_K) 1.
Proof.
  intros RNG p n x H Hx. unfold rng_shcov, shadow_addr in H.
  exact (dcF_shadow1 RNG ASAN_K p (p + n - 1) x H Hx).
Qed.

(* The regions of ctrl_lay_block_contract_F that this run supplies from its own premises: the thread pointer words
   and the thread cells (both in fp_tls, which rng_tls covers), and the shadow of the class-0 and class-1 side-stack
   frames (inside the shadow cover of the side stack). *)
Lemma tls_rng_of_rng_tls : forall RNG m TP, rng_tls RNG m TP -> ctrl_lay_block_tls_rng RNG m TP.
Proof.
  intros RNG m TP H DT TS C T DB k HT. specialize (H DT TS C T DB k HT). unfold fp_tls in H.
  do 3 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [HDT H].
  do 3 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [HTS H]. apply Forall_cons_iff in H as [HC H].
  apply Forall_cons_iff in H as [HT48 H].
  do 5 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [HDB _].
  cbn [fst snd] in HDT, HTS, HC, HT48, HDB.
  split; [eapply rng_sub; [exact HDT | lia | lia]|].
  split; [eapply rng_sub; [exact HTS | lia | lia]|].
  split; [eapply rng_sub; [exact HC | lia | lia]|].
  split; [eapply rng_sub; [exact HT48 | lia | lia] | eapply rng_sub; [exact HDB | lia | lia]].
Qed.

Lemma tp_rng_of_rng_tls : forall RNG m TP cs FS lo hi W D, fp cs m TP FS lo hi W D -> rng_tls RNG m TP ->
  rng RNG (TP - 88) 8 /\ rng RNG (TP - 8) 24.
Proof.
  intros RNG m TP cs FS lo hi W D (DT & TS & C & T & DB & k & HT & _) H.
  specialize (H DT TS C T DB k HT). unfold fp_tls in H.
  do 2 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [H8 H].
  do 3 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [H88 _].
  cbn [fst snd] in H8, H88.
  split; [eapply rng_sub; [exact H88 | lia | lia] | eapply rng_sub; [exact H8 | lia | lia]].
Qed.

Lemma fs_frame_shadow_rng : forall RNG FS c, (c = 0 \/ c = 1)%nat -> rng_shcov RNG FS FS_SIZE ->
  rng RNG (shadow_addr (fs_frame FS c 0)) (fs_M c * fs_B c / 8).
Proof.
  intros RNG FS c Hc H.
  assert (E : fs_M c * fs_B c / 8 = 131072) by (destruct Hc as [-> | ->]; reflexivity).
  assert (Hc' : 0 <= Z.of_nat c <= 1) by (destruct Hc as [-> | ->]; cbn; lia).
  assert (EF : fs_frame FS c 0 = FS + 36864 + Z.of_nat c * 1048576)
    by (unfold fs_frame; change (2 ^ 20) with 1048576; lia).
  rewrite E, EF. unfold shadow_addr.
  pose proof (shcov_span RNG FS FS_SIZE (FS + 36864 + Z.of_nat c * 1048576)
                (FS + 36864 + Z.of_nat c * 1048576 + 1048575) H ltac:(lia) ltac:(lia)
                ltac:(unfold FS_SIZE; lia)) as Hs.
  eapply rng_sub; [exact Hs | lia | Z.div_mod_to_equations; lia].
Qed.

(* Route (C) (a Theorem Labs lane): the 8-aligned shadow-word span of a sub-range lies in that of the range.  Proved here, before
   the section, with Stdlib's lia: inside the section the context holds every rng hypothesis with its divisions. *)
Lemma ae_sh_word_on_sub : forall p n p' n' a, p <= p' -> p' + n' <= p + n -> 0 < n' ->
  sh_word_on p' n' a -> sh_word_on p n a.
Proof.
  intros p n p' n' a H1 H2 H3 (Hn & Ha1 & Ha2).
  unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
  split; [lia|]. split; Z.div_mod_to_equations; lia.
Qed.

(* Route (C) (a Theorem Labs lane): fl_shadow_rw_on of lib/B/ShadowRwOnK.v:13-20 (a Theorem Labs lane), the same statement and proof over
   this file's names.  This file does not Require ShadowRwOnT: loading it (with its closure B.MemNorm, B.MemNormTr,
   ...) makes the OLD `tauto` at the end of atail2's MUf step run without end (measured 2026-10-29 12:3xZ on
   man13-emitasonb: the old text truncated after atail2 compiles in 110-112 s alone, with ShadowRwOn imported, or
   with sh_word_on and the four helper _on files imported, and does not get past that tauto when ShadowRwOnT is
   imported; the first full build sat in it for 40 minutes). *)
Lemma ae_fl_shadow_rw_on : forall P W m m', shadow_rw_on P m -> munch W m m' -> wmono rsegs m m' ->
  (forall x, in_shadow x -> outside W x) -> shadow_rw_on P m'.
Proof.
  intros P W m m' H Hm Hw HW a Hp Ha. destruct (H a Hp Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  exists b. pose proof (rt_shadow_bound _ Ha) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Ha.
Qed.

(* The script below uses this file's lia (em_lia, as ctrl_emit_as.v); the helpers above use Stdlib's lia, which
   adds the Euclidean equations of the divisions. *)
Local Ltac lia ::= em_lia.

Local Ltac mem_after_store_opt ::=
  try rewrite em_le1;
  try fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?mm (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs ?mm A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac fixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* ctrl_emit_as of image B (asan-ubsan build), entry 0x853c4 (CTRL_EMIT_AS of lib/B/Prog/ctrl_emit_as_c.v). *)
Section Emit.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o f md d s g n ns FS : Z) (row tb mb nb gb db sb junk : list byte) (RNG : footprint).

  Local Abbreviation SP0 := (bv_unsigned sp).
  Local Abbreviation LO := (bv_unsigned sp - 4640).
  Local Abbreviation KB := (ly_k row).
  Local Abbreviation LL := (ubat row 21).
  Local Abbreviation GG := (ubat row 22).
  Local Abbreviation AA := (ubat row 23).
  Local Abbreviation CC := (ubat row 20).
  Local Abbreviation RO := (ubat row 18).
  Local Abbreviation RL := (ubat row 19).
  Local Abbreviation EE := (em_E (ubat row 21) (ubat row 22) n (em_hid mb)).
  Local Abbreviation LEN := (em_len (ubat row 21) n).
  Local Abbreviation LB := (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb).
  Local Abbreviation BLK := (fin (ubat row 20) (ubat row 18) (ubat row 19)
                           (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb)).
  Local Abbreviation NM := ((3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\
                            has mb <> 0 /\ rname mb <> 0).
  Local Abbreviation RR := (if em_E (ubat row 21) (ubat row 22) n (em_hid mb) then em_len (ubat row 21) n else 0).
  Local Abbreviation WW := [(bv_unsigned sp - 4640, bv_unsigned sp);
                            (o, o + (if em_E (ubat row 21) (ubat row 22) n (em_hid mb) then em_len (ubat row 21) n else 0))].
  Local Abbreviation DD := [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6);
                            (o, o + (if em_E (ubat row 21) (ubat row 22) n (em_hid mb) then em_len (ubat row 21) n else 0))].

  Hypothesis HMS : asan_memset_contract_F.
  Hypothesis HMC : asan_memcpy_contract_F.
  Hypothesis HLB : ctrl_lay_block_contract_F.
  Hypothesis HBR : reac_braid_encode_ns0_contract_F.
  Hypothesis HFN : ctrl_finish_contract_F.
  Hypothesis Hn : -2^31 <= n < 2^31.
  Hypothesis Hns : -2^31 <= ns < 2^31.
  Hypothesis Hg : 0 <= g < 2^64.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : stk rsegs m LO SP0.
  Hypothesis Dsf : ly_dj LO SP0 f (f + 24).
  Hypothesis Dst : KB = 2 -> ly_dj LO SP0 (ly_tm row) (ly_tm row + 32).
  Hypothesis Dsm : ly_dj LO SP0 md (md + 296).
  Hypothesis Dsn : NM -> ly_dj LO SP0 (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis Dsd : ly_dj LO SP0 d (d + 6).
  Hypothesis Dss : ly_dj LO SP0 s (s + 6).
  Hypothesis Dsg : g <> 0 -> ly_al row <> 0 -> ly_dj LO SP0 g (g + ly_al row).
  Hypothesis Hf0 : f <> 0.
  Hypothesis Hf8 : f mod 8 = 0.
  Hypothesis Hf24 : f + 24 <= 2^64.
  Hypothesis Hrl : length row = 24%nat.
  Hypothesis HR : bytes_at rsegs m f row.
  Hypothesis Hk : KB <= 9.
  Hypothesis Hc : CC <= 2.
  Hypothesis HL : LL <= 2.
  Hypothesis HG : GG <= 1.
  Hypothesis HA : AA <= 1.
  Hypothesis Hao : ly_ao row + ly_al row <= 32.
  Hypothesis Htm : KB = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb.
  Hypothesis Hc2 : CC = 2 -> 2 <= RL /\ RO + RL <= 31.
  Hypothesis HLA : LL = 2 -> AA = 0.
  Hypothesis Hmd0 : md <> 0.
  Hypothesis Hmd8 : md mod 8 = 0.
  Hypothesis Hmd296 : md + 296 <= 2^64.
  Hypothesis Hml : length mb = 296%nat.
  Hypothesis HM : bytes_at rsegs m md mb.
  Hypothesis Hnm : NM -> name_ok nb /\ bytes_at rsegs m (rname mb) nb.
  Hypothesis Ho : 0 < o.
  Hypothesis Ho1492 : o + 1492 <= 2^64.
  Hypothesis HEo : EE = true ->
       rw_cells rsegs m o [CB (Z.to_nat LEN) junk] /\ ly_dj LO SP0 o (o + LEN) /\
       ly_dj o (o + LEN) f (f + 24) /\ (KB = 2 -> ly_dj o (o + LEN) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + LEN) g (g + ly_al row)).
  Hypothesis Hdb : length db = 6%nat.
  Hypothesis HD : bytes_at rsegs m d db.
  Hypothesis Hsb : length sb = 6%nat.
  Hypothesis HSb : bytes_at rsegs m s sb.
  Hypothesis Hgb : g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb.
  Hypothesis Hns0 : AA = 1 -> ns <= 0.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis HAC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= LO.
  Hypothesis HAE : SP0 <= APPMEM_END.
  Hypothesis AWIN : addressable m LO 4640.
  Hypothesis Af : addressable m f 24.
  Hypothesis Amd : addressable m md 296.
  Hypothesis Ad : addressable m d 6.
  Hypothesis As : addressable m s 6.
  Hypothesis APD : app_mem (d + 6) /\ app_mem (d + 7).
  Hypothesis APS : app_mem (s + 6) /\ app_mem (s + 7).
  Hypothesis Atm : KB = 2 -> addressable m (ly_tm row) 32.
  Hypothesis An : NM -> addressable m (rname mb) (Z.of_nat (length nb)).
  Hypothesis Ag : g <> 0 -> ly_al row <> 0 -> addressable m g (ly_al row).
  Hypothesis APg : g <> 0 -> ly_al row <> 0 -> app_mem (g + ly_al row) /\ app_mem (g + 7).
  Hypothesis AO : EE = true -> addressable m o LEN /\ app_mem (o + LEN) /\ (o + LEN <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ14 : KB = 5 -> addressable m JOIN_0014 32.
  Hypothesis AJ13 : KB = 6 -> addressable m JOIN_0013 32.
  Hypothesis FP : fp [0%nat; 1%nat] m (bv_unsigned tp) FS LO SP0 WW DD.
  Hypothesis FPtm : KB = 2 -> fp_dj [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPn : NM -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPg : g <> 0 -> ly_al row <> 0 -> fp_dj [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPT : ctrl_emit_as_tls m (bv_unsigned tp) FS LO SP0.
  (* Footprint premises, discharged in ctrl_emit_as_holds_F from ctrl_emit_as_contract_F. Shadow premises are kept
     QUANTIFIED (byte and 8-aligned-cover forms), so lia never sees a ground / 8 rng fact (internal path, perf note). *)
  Hypothesis FpRB : rng_bytes RNG.
  Hypothesis FpWIN : rng RNG LO 4640.
  Hypothesis FpWSH : forall a b, LO <= a -> a <= b -> b <= SP0 - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpFS : rng RNG FS FS_SIZE.
  Hypothesis FpFSH : forall a b, FS <= a -> a <= b -> b <= FS + FS_SIZE - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis FpGOT : rng RNG GOT_CELL_K 8.
  Hypothesis FpCELL : rng RNG CELL_K 8.
  Hypothesis FpTLS : rng_tls RNG m (bv_unsigned tp).
  Hypothesis FpROW : rng RNG f 24.
  Hypothesis FpSf1 : forall x, f <= x <= f + 23 -> rng RNG (x / 8 + ASAN_K) 1.
  Hypothesis FpSfK : forall a b, f <= a -> a <= b -> b <= f + 23 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpMD : rng RNG md 296.
  Hypothesis FpSmd1 : forall x, md <= x <= md + 295 -> rng RNG (x / 8 + ASAN_K) 1.
  Hypothesis FpSmdK : forall a b, md <= a -> a <= b -> b <= md + 295 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpD : rng RNG d 6.
  Hypothesis FpSdK : forall a b, d <= a -> a <= b -> b <= d + 5 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpS : rng RNG s 6.
  Hypothesis FpSsK : forall a b, s <= a -> a <= b -> b <= s + 5 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpO : EE = true -> rng RNG o LEN.
  Hypothesis FpSo1 : EE = true -> forall x, o <= x <= o + LEN - 1 -> rng RNG (x / 8 + ASAN_K) 1.
  Hypothesis FpSoK : EE = true -> forall a b, o <= a -> a <= b -> b <= o + LEN - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpTM : KB = 2 -> rng RNG (ly_tm row) 32.
  Hypothesis FpTMK : KB = 2 -> forall a b, ly_tm row <= a -> a <= b -> b <= ly_tm row + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpNB : NM -> rng RNG (rname mb) (Z.of_nat (length nb)).
  Hypothesis FpNBK : NM -> forall a b, rname mb <= a -> a <= b -> b <= rname mb + Z.of_nat (length nb) - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpG : g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row).
  Hypothesis FpGK : g <> 0 -> ly_al row <> 0 -> forall a b, g <= a -> a <= b -> b <= g + ly_al row - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpJ14 : KB = 5 -> rng RNG JOIN_0014 32.
  Hypothesis FpSJ14 : KB = 5 -> forall a b, JOIN_0014 <= a -> a <= b -> b <= JOIN_0014 + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis FpJ13 : KB = 6 -> rng RNG JOIN_0013 32.
  Hypothesis FpSJ13 : KB = 6 -> forall a b, JOIN_0013 <= a -> a <= b -> b <= JOIN_0013 + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

  (* The runtime state carried across the body (EE = true regime: the output is [o, o + LEN)): the runtime's cells
     and shadow map, the window and the output marked usable, the side stack for frames (fp) and the thread cells
     apart from the class bytes and the window's shadow (aTL). *)
  Definition aTL (mc : word -> option byte) : Prop := ctrl_emit_as_tls mc (bv_unsigned tp) FS LO SP0.
  Local Abbreviation aWL := [(LO, SP0); (o, o + LEN)].
  Local Abbreviation aDL := [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + LEN)].
  Definition aJ (mc : word -> option byte) : Prop :=
    asan_cells mc /\ shadow_rw mc /\ addressable mc LO 4640 /\ addressable mc o LEN /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 aWL aDL /\ aTL mc.

  (* aJ survives writes inside the window [LO, SP0). *)
  Lemma aJ_win : forall W' m1 m2, aJ m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(LO, SP0)] -> aJ m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & AWo & FPc & TL) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W' FPc MU WM Hs).
    - exact (fl_tls _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* aJ survives writes inside the output [o, o + LEN), when the output is application memory apart from the
     runtime's cells and the side stack's bytes read back after the run. *)
  Lemma aJ_out : forall W' m1 m2, app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) ->
    aJ m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(o, o + LEN)] ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> aJ m2.
  Proof.
    intros W' m1 m2 Hap HRT (AC & SW & AW & AWo & FPc & TL) MU WM Hs RD.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; apply Hs; cbn [outside]; split; [pose proof (app_ivl_meta o (o + LEN) x Hap Hx); lia | exact I]).
    assert (SWW : sub_fp W' aWL)
      by (intros x Hx; apply Hs; cbn [outside] in Hx |- *; destruct Hx as (_ & H2 & _); split; [exact H2 | exact I]).
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply Hs. cbn [outside].
      split; [unfold RT_LO, RT_HI in *; lia | exact I].
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM SWW RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU SWW TL).
  Qed.

  (* aJ survives a callee's writes whose window is inside the window and the output together ([LO, SP0) U
     [o, o + LEN)), when the side stack's bytes read back after the call. *)
  Lemma aJ_wout : forall W' m1 m2, app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) ->
    aJ m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' aWL ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> aJ m2.
  Proof.
    intros W' m1 m2 Hap HRT (AC & SW & AW & AWo & FPc & TL) MU WM Hs RD.
    assert (SHo : forall x, in_shadow x -> outside W' x).
    { intros x Hx. apply Hs. cbn [outside].
      pose proof (app_ivl_meta o (o + LEN) x Hap Hx) as Ho2.
      split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx, HHM; lia
             | split; [lia | exact I]]. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply Hs. cbn [outside].
      split; [unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia
             | split; [unfold RT_LO, RT_HI in *; lia | exact I]].
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM Hs RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* aJ survives a single 1-byte data store inside the output [o, o + LEN): the side stack reads back because the
     write keeps every byte of [FS, FS + FS_SIZE) defined (stk_write). *)
  Lemma aJ_ostore : forall mc (a : Z) (b : byte),
    aJ mc -> app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) -> o <= a < o + LEN ->
    aJ (write_to_mem mc (wa a) [b]).
  Proof.
    intros mc a b AJ API ART Ha.
    pose proof AJ as AJ2. destruct AJ2 as (_ & _ & _ & AOw & FPc & _).
    pose proof AOw as (Ho0 & _ & HoE & _). unfold APPMEM_END in HoE.
    pose proof FPc as FP2. destruct FP2 as (DT & TS & C & T & DB & k & _ & _ & HP & _).
    destruct HP as (_ & _ & _ & _ & P5).
    apply (aJ_out [(a, a + 1)] mc (write_to_mem mc (wa a) [b]) API ART AJ).
    - apply munch_write; cbn [length inside]; [apply munch_refl | lia | lia | left; split; lia].
    - apply wmono_write, wmono_refl.
    - intros x Hx. cbn [outside] in *. destruct Hx as (H1 & _). split; [lia | exact I].
    - intros x Hx. right.
      pose proof (stk_write rsegs mc FS (FS + FS_SIZE) a [b] P5 ltac:(lia) ltac:(cbn [length]; lia)) as STw.
      destruct STw as (_ & _ & STwf). destruct (STwf x Hx) as (_ & HB). exact HB.
  Qed.

  (* A shadow read of the byte o + j from addressable mc o LEN (as declaration_of's da_shadow,
     lib/B/Prog/declaration_of.v): the metadata byte k at (o + j) >> 3 + ASAN_K, and the instrumented check passes. *)
  Lemma afin_sh : forall mc j, addressable mc o LEN -> 0 <= j < LEN ->
    exists k : byte, ov_read_bytes rsegs mc (wa ((o + j) / 8 + ASAN_K)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ (o + j) mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc j AD Hj.
    pose proof (rt_shadow_rd mc o LEN [] AD (fun x _ => I)) as HSR.
    pose proof (rt_addressable mc o LEN AD) as HAD.
    destruct (asan_shadow_read rsegs mc ASAN_K o LEN [] j HSR Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HAD j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A 1-byte shadow read of the byte X = base + j from addressable mc base len. *)
  Lemma a_shadow : forall mc base len X j, addressable mc base len -> 0 <= j < len -> X = base + j ->
    exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc base len X j AD Hj ->.
    pose proof (rt_shadow_rd mc base len [] AD (fun x _ => I)) as HSR.
    pose proof (rt_addressable mc base len AD) as HAD.
    destruct (asan_shadow_read rsegs mc ASAN_K base len [] j HSR Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HAD j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A 4-byte shadow read of the load at X = base + j (not crossing an 8-byte boundary). *)
  Lemma a_shadow4 : forall mc base len X j, addressable mc base len -> 0 <= j -> j + 4 <= len ->
    (base + j) mod 8 + 4 <= 8 -> X = base + j ->
    exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 + 3 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc base len X j AD Hj Hj4 Hm ->.
    pose proof (rt_shadow_rd mc base len [] AD (fun x _ => I)) as HSR.
    pose proof (rt_addressable mc base len AD) as HAD.
    destruct (asan_shadow_read rsegs mc ASAN_K base len [] j HSR ltac:(lia)) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
    pose proof (asan_check_lt rsegs mc ASAN_K base len j 4 k HAD Hj ltac:(lia) ltac:(lia) Hm BK) as OK. lia.
  Qed.

  (* The result written to the output in the EE = true regime: the emitted record, the window flag, and the
     closes relation for the block. *)
  Definition aRES (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0)) BLK LEN)
    /\ (LL <> 2 -> em_wok n = true)
    /\ (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).

  (* The function's postcondition. *)
  Definition aQp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ shadow_rw m' /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (EE = true -> aRES m').

  (* E1 of the glue draft: the prefix lemmas below (afront_hdr .. aentry_k) end at a POST VARIABLE QK instead of
     the function's own post aQp, so that a caller can stop the run at the ctrl_lay_block argument setup
     (0x8571c).  Every path that leaves the prefix without reaching 0x8571c is an EE = false early return
     (aepi0), so HQK0 is all such a caller has to give.  This file's own theorem takes QK := aQp with
     HQK0 := fun _ _ h => h, and the statement of ctrl_emit_as_holds_F does not change. *)
  Variable QK : machine_state -> Prop.
  Hypothesis HQK0 : forall ms, EE = false -> aQp ms -> QK ms.

  (* Stack pointer range, from the incoming stack window. *)
  Lemma arng_sp : 4640 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  (* The six header bytes written at o + 12 .. o + 17 (as in the plain proof's em_fr): the two tag bytes
     136 and 25, the two bytes of a5 (low, high), then row[0] and row[1]. *)
  Local Abbreviation HDR :=
    [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
     Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)].

  (* Real lia including euclidean (div/mod) reasoning; the file's lia is em_lia, which drops div/mod. *)
  Local Ltac rlia := Z.div_mod_to_equations; Zify.zify; xlia zchecker.

  (* The metadata byte of a byte o + j in the output is 0 (marked usable): its whole 8-byte group lies inside
     [o, o + LEN) when 8 <= j and j + 8 <= LEN, so asan_check_8 gives the byte 0. *)
  Lemma a_out0 : forall mc j, addressable mc o LEN -> 8 <= j -> j + 8 <= LEN ->
    exists k : byte, ov_read_bytes rsegs mc (wa ((o + j) / 8 + ASAN_K)) 1 = Some [k] /\ bv_signed k = 0.
  Proof.
    intros mc j AD Hj Hj2.
    pose proof (rt_shadow_rd mc o LEN [] AD (fun x _ => I)) as HSR.
    pose proof (rt_addressable mc o LEN AD) as HAD.
    pose proof (rt_rt3 mc o LEN AD) as HRT3.
    assert (Hiq : 0 <= 8 * ((o + j) / 8) - o < LEN) by rlia.
    destruct (asan_shadow_read rsegs mc ASAN_K o LEN [] (8 * ((o + j) / 8) - o) HSR Hiq) as (k & RK & BK).
    assert (Hdiv : (o + (8 * ((o + j) / 8) - o)) / 8 = (o + j) / 8).
    { replace (o + (8 * ((o + j) / 8) - o)) with (((o + j) / 8) * 8) by rlia.
      rewrite Z.div_mul by rlia. reflexivity. }
    exists k. rewrite Hdiv in RK. split; [exact RK|].
    apply (asan_check_8 rsegs mc ASAN_K o LEN (8 * ((o + j) / 8) - o) k HAD HRT3 ltac:(rlia) ltac:(rlia)
             ltac:(replace (o + (8 * ((o + j) / 8) - o)) with (((o + j) / 8) * 8) by rlia;
                   apply Z.mod_mul; rlia) BK).
  Qed.

  (* Walk an instrumented 1-byte check whose metadata byte k is 0: load it and fall through, because the branch
     to the error path is not taken (k = 0). *)
  Ltac steps_until_if :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
    | _ => idtac
    end.
  Ltac chk0 X k RK K0 RS :=
    let RSh := fresh "RSh" in pose proof RS as RSh;
    step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
    step; step; clear RK RSh; steps_until_if;
    unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (rewrite K0; lia);
    rewrite (proj2 (Z.eqb_eq (bv_signed k) 0) K0); cbn [negb]; cbv iota.

  (* The header stores (0x85658 .. 0x8571c): the six 1-byte stores at o + 12 .. o + 17, each preceded by its
     instrumented check (the byte is in the output [o, o + LEN), marked usable, so the error path is not taken)
     and followed by an overflow guard whose branch to unimp at 0x85810 is not taken because o + 1492 <= 2^64.
     Ends at the ctrl_lay_block argument setup (0x8571c). *)
  Lemma afront_hdr : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
      (mc : word -> option byte) (jf jh : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 jh] ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    (forall (y10 y11 y12 : word) (mc' : word -> option byte),
       munch aWL m mc' ->
       wmono rsegs m mc' -> mem_inv rsegs mc' -> aJ mc' ->
       stk rsegs mc' LO (SP0 + -128) ->
       rw_cells rsegs mc' (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                        C8 s2; C8 s1; C8 s0; C8 ra] ->
       rw_cells rsegs mc' o [CB 6 db] -> rw_cells rsegs mc' (o + 6) [CB 6 sb] ->
       bytes_at rsegs mc' (o + 12) HDR -> wr_at rsegs mc' (o + 12) (Z.of_nat 6) ->
       rw_cells rsegs mc' (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
       evtF rsegs RNG QK
         (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
                  x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
                  (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
                  (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
             F (Z_to_bv 64 0x8571c) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85658) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc jf jh
      HE FR ST MU WM MI AJ P1 P2 P12 P18 Hcont.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (FpO HE) as FpOc.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    pose proof (unsigned_lit o ltac:(lia)) as Hou.
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_bytes rsegs mc (o + 12) 6 jh P12) as (HL12 & _ & HW12). clear P12.
    (* ===== store 1: o + 12 := 136 ===== *)
    step.
    destruct (a_out0 mc 12 AOm ltac:(lia) ltac:(lia)) as (k1 & RK1 & K01).
    chk0 (o + 12) k1 RK1 K01 (FpSo1 HE (o + 12) ltac:(lia)).
    assert (HSa : store_ok rsegs mc (wa (o + 12)) 1 = true).
    { pose proof (wr_at_store_ok rsegs mc (o + 12) (Z.of_nat 6) 0 1%nat HW12 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    step. step. step.
    replace (o + 12 + Z.of_nat 0) with (o + 12) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 136) by lia.
    step. if_false.
    assert (MU1 : munch aWL m (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM1 : wmono rsegs m (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136])) by (apply wmono_write; exact WM).
    assert (MI1 : mem_inv rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply mem_inv_store; [exact MI | cbn [length]; exact HSa]).
    assert (AJ1 : aJ (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply (aJ_ostore mc (o + 12) (Z_to_bv 8 136)); [exact AJ | exact API | exact ART | lia]).
    assert (FR1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST1 : stk rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) LO (SP0 + -128))
      by (apply stk_write; [exact ST | lia | cbn [length]; lia]).
    assert (P1_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HB1 : bytes_at rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 12) [Z_to_bv 8 136])
      by (apply bytes_at_write_same; cbn [length]; lia).
    assert (HW1 : wr_at rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW12).
    try fold (wa (o + 12)).
    set (m1 := write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) in *. clearbody m1.
    pose proof AJ1 as AJ1c. destruct AJ1c as (_ & _ & _ & AO1 & _ & _).
    (* ===== store 2: o + 13 := 25 ===== *)
    step.
    destruct (a_out0 m1 13 AO1 ltac:(lia) ltac:(lia)) as (k2 & RK2 & K02).
    chk0 (o + 13) k2 RK2 K02 (FpSo1 HE (o + 13) ltac:(lia)).
    assert (HSok2 : store_ok rsegs m1 (wa (o + 13)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m1 (o + 12) (Z.of_nat 6) 1 1%nat HW1 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 1) with (o + 13) in H by lia. exact H. }
    step. step. step.
    replace (o + 13 + Z.of_nat 0) with (o + 13) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 25) by lia.
    step. if_false.
    assert (MU2 : munch aWL m (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply munch_write; [exact MU1 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM2 : wmono rsegs m (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25])) by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply mem_inv_store; [exact MI1 | cbn [length]; exact HSok2]).
    assert (AJ2 : aJ (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply (aJ_ostore m1 (o + 13) (Z_to_bv 8 25)); [exact AJ1 | exact API | exact ART | lia]).
    assert (FR2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR1 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST2 : stk rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) LO (SP0 + -128))
      by (apply stk_write; [exact ST1 | lia | cbn [length]; lia]).
    assert (P1_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_1 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW2 : wr_at rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW1).
    assert (HBy2 : bytes_at rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 12)
                     [Z_to_bv 8 136; Z_to_bv 8 25]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25] with ([Z_to_bv 8 136] ++ [Z_to_bv 8 25]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 1) with (o + 13) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 13)).
    set (m2 := write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) in *. clearbody m2.
    pose proof AJ2 as AJ2c. destruct AJ2c as (_ & _ & _ & AO2 & _ & _).
    (* ===== store 3: o + 14 := low byte of a5 ===== *)
    step.
    destruct (a_out0 m2 14 AO2 ltac:(lia) ltac:(lia)) as (k3 & RK3 & K03).
    chk0 (o + 14) k3 RK3 K03 (FpSo1 HE (o + 14) ltac:(lia)).
    assert (HSc : store_ok rsegs m2 (wa (o + 14)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m2 (o + 12) (Z.of_nat 6) 2 1%nat HW2 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 2) with (o + 14) in H by lia. exact H. }
    step. step.
    replace (o + 14 + Z.of_nat 0) with (o + 14) by lia.
    rewrite ?em_le1. rewrite (em_c16_lo a5).
    step. if_false.
    assert (MU3 : munch aWL m (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply munch_write; [exact MU2 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM3 : wmono rsegs m (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply wmono_write; exact WM2).
    assert (MI3 : mem_inv rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply mem_inv_store; [exact MI2 | cbn [length]; exact HSc]).
    assert (AJ3 : aJ (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply (aJ_ostore m2 (o + 14) (Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)));
          [exact AJ2 | exact API | exact ART | lia]).
    assert (FR3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR2 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST3 : stk rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    LO (SP0 + -128)) by (apply stk_write; [exact ST2 | lia | cbn [length]; lia]).
    assert (P1_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    o [CB 6 db]) by (apply rw_cells_frame; [exact P1_2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (o + 6) [CB 6 sb]) by (apply rw_cells_frame; [exact P2_2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                      (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_2 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW3 : wr_at rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (o + 12) (Z.of_nat 6)) by (apply wr_at_write; exact HW2).
    assert (HBy3 : bytes_at rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                     (o + 12) [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25] ++ [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy2 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 2) with (o + 14) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 14)).
    set (m3 := write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]) in *. clearbody m3.
    pose proof AJ3 as AJ3c. destruct AJ3c as (_ & _ & _ & AO3 & _ & _).
    (* ===== store 4: o + 15 := high byte of a5 ===== *)
    step.
    destruct (a_out0 m3 15 AO3 ltac:(lia) ltac:(lia)) as (k4 & RK4 & K04).
    chk0 (o + 15) k4 RK4 K04 (FpSo1 HE (o + 15) ltac:(lia)).
    assert (HSd : store_ok rsegs m3 (wa (o + 15)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m3 (o + 12) (Z.of_nat 6) 3 1%nat HW3 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 3) with (o + 15) in H by lia. exact H. }
    step. step. step.
    replace (o + 15 + Z.of_nat 0) with (o + 15) by lia.
    rewrite ?em_le1. rewrite (em_c16_hi a5).
    step. if_false.
    assert (MU4 : munch aWL m (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply munch_write; [exact MU3 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM4 : wmono rsegs m (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply wmono_write; exact WM3).
    assert (MI4 : mem_inv rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply mem_inv_store; [exact MI3 | cbn [length]; exact HSd]).
    assert (AJ4 : aJ (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply (aJ_ostore m3 (o + 15) (Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)));
          [exact AJ3 | exact API | exact ART | lia]).
    assert (FR4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR3 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST4 : stk rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    LO (SP0 + -128)) by (apply stk_write; [exact ST3 | lia | cbn [length]; lia]).
    assert (P1_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    o [CB 6 db]) by (apply rw_cells_frame; [exact P1_3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (o + 6) [CB 6 sb]) by (apply rw_cells_frame; [exact P2_3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                      (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_3 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW4 : wr_at rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (o + 12) (Z.of_nat 6)) by (apply wr_at_write; exact HW3).
    assert (HBy4 : bytes_at rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                     (o + 12) [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
                               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
              Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]
              ++ [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy3 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 3) with (o + 15) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 15)).
    set (m4 := write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]) in *. clearbody m4.
    pose proof AJ4 as AJ4c. destruct AJ4c as (_ & _ & _ & AO4 & _ & _).
    (* ===== store 5: o + 16 := row[0] ===== *)
    step.
    destruct (a_out0 m4 16 AO4 ltac:(lia) ltac:(lia)) as (k5 & RK5 & K05).
    chk0 (o + 16) k5 RK5 K05 (FpSo1 HE (o + 16) ltac:(lia)).
    assert (HSe : store_ok rsegs m4 (wa (o + 16)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m4 (o + 12) (Z.of_nat 6) 4 1%nat HW4 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 4) with (o + 16) in H by lia. exact H. }
    step. step.
    replace (o + 16 + Z.of_nat 0) with (o + 16) by lia.
    rewrite ?em_le1. rewrite (em_byte_zxb (nth 0 row (Z_to_bv 8 0))).
    step. if_false.
    assert (MU5 : munch aWL m (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply munch_write; [exact MU4 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM5 : wmono rsegs m (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply wmono_write; exact WM4).
    assert (MI5 : mem_inv rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply mem_inv_store; [exact MI4 | cbn [length]; exact HSe]).
    assert (AJ5 : aJ (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply (aJ_ostore m4 (o + 16) (nth 0 row (Z_to_bv 8 0))); [exact AJ4 | exact API | exact ART | lia]).
    assert (FR5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR4 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST5 : stk rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) LO (SP0 + -128))
      by (apply stk_write; [exact ST4 | lia | cbn [length]; lia]).
    assert (P1_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_4 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW5 : wr_at rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW4).
    assert (HBy5 : bytes_at rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 12)
                     [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
                      Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
              Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)] ++ [nth 0 row (Z_to_bv 8 0)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy4 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 4) with (o + 16) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 16)).
    set (m5 := write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) in *. clearbody m5.
    pose proof AJ5 as AJ5c. destruct AJ5c as (_ & _ & _ & AO5 & _ & _).
    (* ===== store 6: o + 17 := row[1] (no overflow guard) ===== *)
    step.
    destruct (a_out0 m5 17 AO5 ltac:(lia) ltac:(lia)) as (k6 & RK6 & K06).
    chk0 (o + 17) k6 RK6 K06 (FpSo1 HE (o + 17) ltac:(lia)).
    assert (HSf : store_ok rsegs m5 (wa (o + 17)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m5 (o + 12) (Z.of_nat 6) 5 1%nat HW5 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 5) with (o + 17) in H by lia. exact H. }
    step.
    replace (o + 17 + Z.of_nat 0) with (o + 17) by lia.
    rewrite ?em_le1. rewrite (em_byte_zxb (nth 1 row (Z_to_bv 8 0))).
    assert (MU6 : munch aWL m (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply munch_write; [exact MU5 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM6 : wmono rsegs m (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply wmono_write; exact WM5).
    assert (MI6 : mem_inv rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply mem_inv_store; [exact MI5 | cbn [length]; exact HSf]).
    assert (AJ6 : aJ (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply (aJ_ostore m5 (o + 17) (nth 1 row (Z_to_bv 8 0))); [exact AJ5 | exact API | exact ART | lia]).
    assert (FR6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR5 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST6 : stk rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) LO (SP0 + -128))
      by (apply stk_write; [exact ST5 | lia | cbn [length]; lia]).
    assert (P1_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_5 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW6 : wr_at rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW5).
    assert (HBy6 : bytes_at rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 12) HDR).
    { change HDR with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)] ++ [nth 1 row (Z_to_bv 8 0)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy5 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 5) with (o + 17) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 17)).
    set (m6 := write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) in *. clearbody m6.
    (* ===== reached the ctrl_lay_block argument setup (0x8571c) ===== *)
    simp_regs.
    apply (Hcont _ _ _ m6 MU6 WM6 MI6 AJ6 ST6 FR6 P1_6 P2_6 HBy6 HW6 P18_6).
  Qed.

  (* sub_fp of a narrower window [lo', SP0) inside the function window [LO, SP0). *)
  Lemma ain_sub : forall lo', LO <= lo' -> sub_fp [(lo', SP0)] [(LO, SP0)].
  Proof. intros lo' H x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* The asan facts in a memory that differs from m only inside the window [LO, SP0). *)
  Lemma atr : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ shadow_rw mc /\ fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p q, addressable m p q -> addressable mc p q).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split]].
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fl_shadow_rw W' m mc HSW MU WM SHo).
    - exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
    - intros p q H. exact (fl_addressable W' m mc p q H MU SHo).
  Qed.

  (* The epilogue (0x857c8 .. 0x85804): the return value RR (held in s9), the register restores and ret. *)
  Lemma aepi : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte) (r : Z),
    r = RR -> 0 <= r < 2^64 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw mc -> addressable mc LO 4640 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD ->
    (EE = true -> aRES mc) ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 (Z_to_bv 64 r) x26 x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x857c8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 u3 u4 u5 u6
      mc j r Er Rr FR ST MU WM MI AC SW AW FP' HRES.
    pose proof arng_sp as Rsp.
    pose proof ST as (Rlo & _ & _).
    do 16 step.
    apply evtF_done. unfold aQp.
    do 14 eexists. exists mc. rewrite Er.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP'|].
    exact HRES.
  Qed.

  (* The early return (EE = false): the epilogue with RR = 0 (held in s9) and no block written. *)
  Lemma aepi0 : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    EE = false ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 (Z_to_bv 64 0) x26 x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x857c8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 u3 u4 u5 u6
      mc j HE FR ST MU WM MI.
    pose proof arng_sp as Rsp.
    destruct (atr _ mc MU WM (ain_sub LO ltac:(lia))) as (AC & SW & FP' & ADT).
    apply (aepi x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
             u3 u4 u5 u6 mc j 0);
      [rewrite HE; reflexivity | lia | exact FR | exact ST | | exact WM | exact MI
       | exact AC | exact SW | exact (ADT _ _ AWIN) | exact FP' | rewrite HE; intros H; discriminate H].
    apply (munch_weaken [(LO, SP0)]); [|exact MU].
    intros x Hx. rewrite HE in Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I].
  Qed.

  (* fp for the ctrl_lay_block call: the callee's frame [SP0 + -128 - K, SP0 + -128) and its block window
     [o + 18, o + 50) lie inside this function's window and output; fl_fp_sub shrinks aJ's fp to it. *)
  Lemma alay_fp : forall mc, 52 <= LEN ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 aWL aDL ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128)
      (ctrl_lay_block_W o (SP0 + -128)) (ctrl_lay_block_D o f).
  Proof.
    intros mc HLe FPc.
    apply (fl_fp_sub [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 aWL aDL
             (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128)
             (ctrl_lay_block_W o (SP0 + -128)) (ctrl_lay_block_D o f) FPc).
    - unfold CTRL_LAY_BLOCK_K. lia.
    - lia.
    - intros X HX. unfold ctrl_lay_block_W, CTRL_LAY_BLOCK_K.
      apply fl_dj_cons in HX as [HX1 HX2]. apply fl_dj_cons in HX2 as [HX2 _].
      apply fl_dj_cons. split.
      + apply (fl_dj_sub _ _ _ _ _ HX1); lia.
      + apply (fl_dj_sub _ _ _ _ _ HX2); lia.
    - intros X HX. unfold ctrl_lay_block_D.
      apply fl_dj_cons in HX as [HXf HX]. apply fl_dj_cons in HX as [_ HX].
      apply fl_dj_cons in HX as [_ HX]. apply fl_dj_cons in HX as [_ HX].
      apply fl_dj_cons in HX as [HXo _].
      apply fl_dj_cons. split.
      + exact HXf.
      + apply (fl_dj_sub _ _ _ _ _ HXo); lia.
  Qed.

  (* ctrl_lay_block_tls for the call: its shadow window [shadow LO, shadow (SP0 + -128)) is inside aTL's
     [shadow LO, shadow SP0); fl_dj_last shrinks the apartness. *)
  Lemma alay_tls : forall mc, ctrl_emit_as_tls mc (bv_unsigned tp) FS LO SP0 ->
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128).
  Proof.
    intros mc TL. unfold ctrl_lay_block_tls. intros DT TS C T DB k HT.
    unfold ctrl_emit_as_tls in TL. pose proof (TL DT TS C T DB k HT) as H.
    apply (fl_dj_last (fp_tls (bv_unsigned tp) DT TS C T DB k) (fp_w [0%nat; 1%nat] FS)
             (shadow_addr LO) (shadow_addr SP0)
             (shadow_addr (SP0 + -128 - CTRL_LAY_BLOCK_K)) (shadow_addr (SP0 + -128)) H).
    - unfold shadow_addr, CTRL_LAY_BLOCK_K.
      assert (LO / 8 <= (SP0 + -128 - 4512) / 8) by (apply Z.div_le_mono; lia). lia.
    - unfold shadow_addr.
      assert ((SP0 + -128) / 8 <= SP0 / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.

  (* outside is pointwise on a concatenation (the converse of alay_oai below). *)
  Lemma alay_oapp : forall A B x, outside A x -> outside B x -> outside (A ++ B) x.
  Proof.
    induction A as [|[lo hi] A IH]; intros B x HoA HoB; cbn [app outside] in *; [exact HoB|].
    destruct HoA as [H1 H2]. split; [exact H1 | exact (IH B x H2 HoB)].
  Qed.

  (* The rng_tls premise survives the writes of this run. The run writes only inside
     aWL ++ fp_w [0; 1] FS ++ [(shadow LO, shadow SP0)]; the fp premise puts the thread cells apart from aWL and
     the ctrl_emit_as_tls premise puts them apart from the other two, so the cells keep their bytes and the
     pointers read from them are the ones of the entry state (fl_tls_same). The rng facts then transport. *)
  Lemma aTR_keep : forall (W D W' : list ivl) (m1 m2 : word -> option byte),
    fp [0%nat; 1%nat] m1 (bv_unsigned tp) FS LO SP0 W D ->
    ctrl_emit_as_tls m1 (bv_unsigned tp) FS LO SP0 ->
    munch W' m1 m2 -> sub_fp W' (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) ->
    rng_tls RNG m1 (bv_unsigned tp) -> rng_tls RNG m2 (bv_unsigned tp).
  Proof.
    intros W D W' m1 m2 FPc TLc MU Hs HRtls DT TS C T DB k HT.
    pose proof FPc as FPd.
    destruct FPd as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    (* every byte of every fp_tls range is outside aWL (fp) and outside the rest (ctrl_emit_as_tls) *)
    pose proof (fl_cols W W _ HWd (fun x h => h)) as HcA. apply Forall_app in HcA as [HcA _].
    pose proof (TLc DT0 TS0 C0 T0 DB0 k0 HT0) as HcB.
    assert (Hcols : Forall (fun dd : ivl => forall x, fst dd <= x < snd dd -> outside W' x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { rewrite Forall_forall in HcA |- *. intros dd Hin x Hx. apply Hs.
      apply alay_oapp; [exact (HcA dd Hin x Hx)|].
      exact (fl_dj_out_r _ _ (fst dd) (snd dd) x HcB
               ltac:(destruct dd; exact Hin) Hx). }
    destruct (fl_tls_same m1 m2 W' (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT MU Hcols)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact (HRtls DT TS C T DB k HT0).
  Qed.

  (* ---- The return-side transport of aJ across the ctrl_lay_block call. This call's write window carries fp_w
     and the stack shadow, so aJ_win / aJ_out / aJ_wout do not apply; aJ_lay is the mirror of alay_fp / alay_tls.
     The callee's post (ctrl_lay_block_c.v) gives asan_cells, shadow_rw, the callee window addressable and the
     returned fp; the output and the saved-register frame [SP0 + -128, SP0) keep their shadow, so they transport,
     and fl_fp_ret / fl_tls_same carry the fp and tls back over [LO, SP0). ---- *)

  (* The ctrl_lay_block post's munch window (block at o, callee sp = SP0 + -128). *)
  Local Abbreviation aWlay :=
    ([(o + 18, o + 50); (SP0 + -128 - CTRL_LAY_BLOCK_K, SP0 + -128)] ++ fp_w [0%nat; 1%nat] FS ++
     [(shadow_addr (SP0 + -128 - CTRL_LAY_BLOCK_K), shadow_addr (SP0 + -128))]).

  Lemma alay_oai : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
  Proof.
    induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
    destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
  Qed.

  Lemma alay_ajoin : forall mc p q q', addressable mc p q -> addressable mc (p + q) q' -> 0 <= q' ->
    addressable mc p (q + q').
  Proof.
    intros mc p q q' (Hp0 & Hpn & Hpe & HpA) (Hr0 & Hrn & Hre & HrA) Hq.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_le_dec i q) as [L|L]; [apply HpA; lia|].
    replace (p + i) with (p + q + (i - q)) by lia. apply HrA. lia.
  Qed.

  Lemma alay_akeep : forall W mc m' p q, addressable mc p q -> munch W mc m' ->
    (forall i, 0 <= i < q -> outside W (shadow_addr (p + i))) -> addressable m' p q.
  Proof.
    intros W mc m' p q (Hk0 & Hkn & Hke & HkA) MU HW. split; [exact Hk0|]. split; [exact Hkn|]. split; [exact Hke|].
    intros i Hi. destruct (HkA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
    pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
    unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
  Qed.

  Lemma alay_shlt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
  Proof. unfold shadow_addr. intros x L HLd Hx. lia. Qed.

  Lemma alay_shge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
  Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

  Lemma alay_wsh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
    ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
  Proof.
    intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
    - pose proof (alay_shlt x lo Hm L). lia.
    - pose proof (alay_shge x hi ltac:(lia)). lia.
  Qed.

  Lemma alay_shout : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END ->
    ~ (shadow_addr a <= x < shadow_addr b).
  Proof.
    intros x a b Hx Ha Hb. unfold shadow_addr.
    pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
    pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
    replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
    unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  Qed.

  Lemma alay_fr0mod8 : FS mod 4096 = 0 -> fs_frame FS 0 0 mod 8 = 0.
  Proof.
    intros H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    repeat (match goal with |- context[2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end).
    lia.
  Qed.

  Lemma alay_fr1mod8 : FS mod 4096 = 0 -> fs_frame FS 1 0 mod 8 = 0.
  Proof.
    intros H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    repeat (match goal with |- context[2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end).
    lia.
  Qed.

  Lemma alay_fpw_bnd : forall c, (c = 0 \/ c = 1)%nat ->
    FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + FS_SIZE /\
    FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + FS_SIZE /\
    FS <= fs_frame FS c 0 /\ fs_frame FS c (fs_M c) <= FS + FS_SIZE.
  Proof.
    intros c Hcc. destruct Hcc as [-> | ->];
      (unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B, FS_SIZE; cbn [Z.of_nat Pos.of_succ_nat];
       repeat (match goal with |- context[2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end);
       repeat split; lia).
  Qed.

  Lemma alay_fsh : forall x, app_mem x ->
    FS mod 4096 = 0 -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
    outside (fp_w [0%nat; 1%nat] FS) x -> outside (fp_w [0%nat; 1%nat] FS) (shadow_addr x).
  Proof.
    intros x Hap Hmod Happ Hout.
    pose proof (rt_app_shadow x Hap) as Hs.
    destruct (alay_fpw_bnd 0%nat (or_introl eq_refl)) as (B0a & B0b & B0c & B0d & B0e & B0f).
    destruct (alay_fpw_bnd 1%nat (or_intror eq_refl)) as (B1a & B1b & B1c & B1d & B1e & B1f).
    pose proof (alay_fr0mod8 Hmod) as M0. pose proof (alay_fr1mod8 Hmod) as M1.
    cbn [fp_w flat_map fp_w1 app outside] in Hout |- *.
    destruct Hout as (_ & _ & F0 & _ & _ & _ & F1 & _).
    assert (AI : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> ~ (lo <= shadow_addr x < hi)).
    { intros lo hi Hl Hh Hin. destruct (app_ivl_meta lo hi (shadow_addr x)
        (fun z Hz => Happ z ltac:(lia)) Hs); lia. }
    repeat split.
    - apply AI; lia.
    - apply AI; lia.
    - apply AI; lia.
    - apply alay_wsh; [exact M0 | exact F0].
    - apply AI; lia.
    - apply AI; lia.
    - apply AI; lia.
    - apply alay_wsh; [exact M1 | exact F1].
  Qed.

  Lemma alay_outfpw_hi : forall Z, app_mem Z -> 0 < FS -> FS mod 4096 = 0 ->
    FS + FS_SIZE <= Z -> Z <= APPMEM_END -> outside (fp_w [0%nat; 1%nat] FS) Z.
  Proof.
    intros Z Hap FSpos Hmod HZ HZa.
    destruct (alay_fpw_bnd 0%nat (or_introl eq_refl)) as (B0a & B0b & B0c & B0d & B0e & B0f).
    destruct (alay_fpw_bnd 1%nat (or_intror eq_refl)) as (B1a & B1b & B1c & B1d & B1e & B1f).
    cbn [fp_w flat_map fp_w1 app outside].
    repeat split; first [ exact I | lia | (apply alay_shout; [exact Hap | lia | lia]) ].
  Qed.

  Lemma alay_fs : 0 < FS /\ FS mod 4096 = 0 /\ (forall a, FS <= a < FS + FS_SIZE -> app_mem a) /\ FS + FS_SIZE <= LO.
  Proof.
    destruct FP as (DT_ & TS_ & C_ & T_ & DB_ & k_ & _ & _ & FSP & _ & _ & _ & FSL & _ & _ & _).
    destruct FSP as (FSpos & FSmod & _ & FSapp & _).
    repeat split; assumption.
  Qed.

  Lemma alay_sh : forall Z, app_mem Z ->
    app_ivl o (o + LEN) -> app_ivl LO SP0 ->
    FS mod 4096 = 0 -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
    outside (fp_w [0%nat; 1%nat] FS) Z ->
    (Z < SP0 + -128 - CTRL_LAY_BLOCK_K \/ SP0 + -128 <= Z) ->
    52 <= LEN ->
    outside aWlay (shadow_addr Z).
  Proof.
    intros Z HapZ AIo AIw Hmod Happ Hfpw Hz HLe.
    pose proof (rt_app_shadow Z HapZ) as Hs.
    apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [|split; [|exact I]].
      + intros Hin. destruct (app_ivl_meta (o + 18) (o + 50) (shadow_addr Z)
          (app_ivl_sub o (o + LEN) (o + 18) (o + 50) AIo ltac:(lia) ltac:(lia)) Hs); lia.
      + intros Hin. destruct (app_ivl_meta (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) (shadow_addr Z)
          (app_ivl_sub LO SP0 (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) AIw
             ltac:(unfold CTRL_LAY_BLOCK_K; lia) ltac:(lia)) Hs); lia.
    - exact (alay_fsh Z HapZ Hmod Happ Hfpw).
    - cbn [outside]. split; [|exact I]. apply alay_wsh.
      + unfold CTRL_LAY_BLOCK_K. lia.
      + intros [HH1 HH2]. destruct Hz as [Hzd|Hzd]; unfold CTRL_LAY_BLOCK_K in *; lia.
  Qed.

  (* aJ at the ctrl_lay_block call's return: the callee's post (asan_cells, shadow_rw, its window addressable and
     its fp) with aJ mc. *)
  Lemma aJ_lay : forall (mc m1 : word -> option byte) (W' D' : list ivl),
    EE = true -> 52 <= LEN ->
    aJ mc -> munch aWlay mc m1 ->
    asan_cells m1 -> shadow_rw m1 ->
    addressable m1 (SP0 + -128 - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    fp [0%nat; 1%nat] m1 (bv_unsigned tp) FS (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) W' D' ->
    aJ m1.
  Proof.
    intros mc m1 W' D' HE HLe AJ MU AC1 SW1 AWc1 FP1.
    destruct AJ as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    pose proof arng_sp as RSP.
    pose proof (addressable_app mc o LEN AOm) as AIo.
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as AIw0.
      apply (app_ivl_sub LO (LO + 4640) LO SP0 AIw0); lia. }
    assert (HIno : In (o, o + LEN) aDL) by (cbn [In]; right; right; right; right; left; reflexivity).
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    pose proof FPm as FPd.
    destruct FPd as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    assert (SUB : sub_fp aWlay (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)])).
    { intros x Hx. cbn [outside app] in Hx. destruct Hx as (Hlo & Ho_ & Hrest).
      destruct (alay_oai (fp_w [0%nat; 1%nat] FS) [(shadow_addr LO, shadow_addr SP0)] x Hrest) as (Hfpw_x & HY_x).
      cbn [outside] in HY_x. destruct HY_x as (HYx & _).
      apply fl_out_app; [| apply fl_out_app].
      - cbn [outside]. split; [|split; [|exact I]].
        + intros [A1 A2]. apply Ho_; lia.
        + intros [A1 A2]. apply Hlo; unfold CTRL_LAY_BLOCK_K in *; lia.
      - exact Hfpw_x.
      - cbn [outside]. split; [|exact I]. intros [A1 A2]. apply HYx. split.
        + replace (shadow_addr LO) with (shadow_addr (SP0 + -128 - CTRL_LAY_BLOCK_K));
            [exact A1 | f_equal; unfold CTRL_LAY_BLOCK_K; lia].
        + pose proof (alay_shge SP0 (SP0 + -128) ltac:(lia)) as G. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - exact AC1.
    - exact SW1.
    - assert (AWlo : addressable m1 LO CTRL_LAY_BLOCK_K).
      { replace LO with (SP0 + -128 - CTRL_LAY_BLOCK_K) by (unfold CTRL_LAY_BLOCK_K; lia). exact AWc1. }
      assert (AWfr : addressable m1 (LO + CTRL_LAY_BLOCK_K) 128).
      { apply (alay_akeep aWlay mc m1 (LO + CTRL_LAY_BLOCK_K) 128).
        - apply (addressable_sub mc LO 4640 CTRL_LAY_BLOCK_K 128 AWm); unfold CTRL_LAY_BLOCK_K; lia.
        - exact MU.
        - intros i Hi. apply (alay_sh (LO + CTRL_LAY_BLOCK_K + i)).
          + apply AIwS; unfold CTRL_LAY_BLOCK_K in *; lia.
          + exact AIo.
          + exact AIwS.
          + exact Fmod.
          + exact Fapp.
          + apply alay_outfpw_hi.
            * apply AIwS; unfold CTRL_LAY_BLOCK_K in *; lia.
            * exact FSpos.
            * exact Fmod.
            * unfold CTRL_LAY_BLOCK_K in *; lia.
            * unfold CTRL_LAY_BLOCK_K in *; lia.
          + right; unfold CTRL_LAY_BLOCK_K in *; lia.
          + exact HLe. }
      exact (alay_ajoin m1 LO CTRL_LAY_BLOCK_K 128 AWlo AWfr ltac:(lia)).
    - apply (alay_akeep aWlay mc m1 o LEN AOm MU).
      intros i Hi. apply (alay_sh (o + i)).
      + apply AIo; lia.
      + exact AIo.
      + exact AIwS.
      + exact Fmod.
      + exact Fapp.
      + exact (fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) o (o + LEN) (o + i) HDd HIno ltac:(lia)).
      + destruct DsoLO as [Hdj|Hdj]; [right; lia | left; unfold CTRL_LAY_BLOCK_K in *; lia].
      + exact HLe.
    - exact (fl_fp_ret [0%nat; 1%nat] mc m1 (bv_unsigned tp) FS LO SP0 aWL aDL
               [(shadow_addr LO, shadow_addr SP0)] aWlay
               (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) W' D' FPm TLm MU SUB FP1).
    - unfold aTL, ctrl_emit_as_tls. intros DT TS C T DB k HT1.
      destruct FPm as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
      assert (Htc : Forall (fun d => forall y, fst d <= y < snd d -> outside aWlay y)
                     (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
      { apply Forall_forall. intros [a b] Hin y Hy. apply SUB. apply fl_out_app.
        - exact (fl_dj_out aWL _ a b y HWd (in_or_app _ _ _ (or_introl Hin)) Hy).
        - exact (fl_dj_out_r _ _ a b y (TLm _ _ _ _ _ _ HT0) Hin Hy). }
      destruct (fl_tls_same mc m1 aWlay (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT1 MU Htc)
        as (E1 & E2 & E3 & E4 & E5 & E6).
      subst. exact (TLm DT TS C T DB k HT0).
  Qed.

  (* The function window base is 8-aligned (SP0 is 16-aligned, 4640 is a multiple of 8). *)
  Lemma aLOmod8 : LO mod 8 = 0.
  Proof. pose proof HS16 as H. rlia. Qed.

  (* The three spill slots at the frame base [SP0 + -128, SP0 + -128 + 24) read back as three 8-byte words:
     the junk block CB 24 (le8 w0 ++ le8 w1 ++ le8 w2) is the three cells C8 w0, C8 w1, C8 w2. *)
  Lemma arw_cb3 : forall mc A w0 w1 w2 cs,
    rw_cells rsegs mc A (CB 24 (le8 w0 ++ le8 w1 ++ le8 w2) :: cs) ->
    rw_cells rsegs mc A (C8 w0 :: C8 w1 :: C8 w2 :: cs).
  Proof.
    intros mc A w0 w1 w2 cs [[Hwf Hb] Hw].
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [_ Hcs].
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [exact I|]. split; [exact I|]. split; [exact I|]. exact Hcs.
    - cbn [cells_bytes cbytes] in Hb |- *. rewrite <- !app_assoc in Hb. exact Hb.
    - cbn [cells_size csize] in Hw |- *.
      replace (8 + (8 + (8 + cells_size cs)))%nat with (24 + cells_size cs)%nat by lia. exact Hw.
  Qed.

  (* The reverse: three 8-byte cells merge into a 24-byte junk block (for the atail2 hand-off). *)
  Lemma arw_cb3' : forall mc A w0 w1 w2 cs,
    rw_cells rsegs mc A (C8 w0 :: C8 w1 :: C8 w2 :: cs) ->
    rw_cells rsegs mc A (CB 24 (le8 w0 ++ le8 w1 ++ le8 w2) :: cs).
  Proof.
    intros mc A w0 w1 w2 cs [[Hwf Hb] Hw].
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [_ [_ [_ Hcs]]].
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite !length_app, !length_le8; reflexivity | exact Hcs].
    - cbn [cells_bytes cbytes] in Hb |- *. rewrite <- !app_assoc. exact Hb.
    - cbn [cells_size csize] in Hw |- *.
      replace (24 + cells_size cs)%nat with (8 + (8 + (8 + cells_size cs)))%nat by lia. exact Hw.
  Qed.

  (* Transport of bytes_at for an application-memory region apart from the window [LO, SP0), the output
     [o, o + LEN), the side stack and (being application memory) the window's shadow, across the entry-to-call
     writes (munch of aWL, the side stack and the stack shadow). *)
  Lemma akeep_bytes : forall A q (bs : list byte) mc,
    bytes_at rsegs m A bs -> Z.of_nat (length bs) = q ->
    app_ivl A (A + q) ->
    (A + q <= LO \/ SP0 <= A) -> (A + q <= o \/ o + LEN <= A) ->
    (forall x, A <= x < A + q -> outside (fp_w [0%nat; 1%nat] FS) x) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    bytes_at rsegs mc A bs.
  Proof.
    intros A q bs mc HB Hq AI Hw Ho2 Hfpw MU.
    apply (fl_bytes _ m mc A bs HB MU).
    intros x Hx. rewrite Hq in Hx.
    apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [|split; [|exact I]].
      + intro C; destruct Hw; lia.
      + intro C; destruct Ho2; lia.
    - apply Hfpw. lia.
    - cbn [outside]. split; [|exact I].
      pose proof (alay_shout x LO SP0 (AI x ltac:(lia)) ltac:(unfold HIGHMEM_BEG in HHM; lia) HAE) as H. lia.
  Qed.

  (* Transport of addressable for an application-memory region apart from the window [LO, SP0) and the side
     stack, across the entry-to-call writes: its shadow bytes keep their value (alay_akeep). *)
  Lemma akeep_addr : forall A q mc,
    addressable m A q -> app_ivl A (A + q) -> app_ivl o (o + LEN) ->
    (A + q <= LO \/ SP0 <= A) ->
    (forall x, A <= x < A + q -> outside (fp_w [0%nat; 1%nat] FS) x) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    addressable mc A q.
  Proof.
    intros A q mc AD AI AIo Hw Hfpw MU.
    apply (alay_akeep (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc A q AD MU).
    intros i Hi.
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    assert (AIw : app_ivl LO SP0).
    { pose proof (addressable_app m LO 4640 AWIN) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    pose proof (rt_app_shadow (A + i) (AI (A + i) ltac:(lia))) as Hs.
    apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [|split; [|exact I]].
      + destruct (app_ivl_meta LO SP0 (shadow_addr (A + i)) AIw Hs); lia.
      + destruct (app_ivl_meta o (o + LEN) (shadow_addr (A + i)) AIo Hs); lia.
    - exact (alay_fsh (A + i) (AI (A + i) ltac:(lia)) Fmod Fapp (Hfpw (A + i) ltac:(lia))).
    - cbn [outside]. split; [|exact I].
      pose proof (alay_wsh (A + i) LO SP0 aLOmod8 ltac:(destruct Hw; lia)) as W. lia.
  Qed.

  (* A shadow address of a non-negative address is at least ASAN_K (the shadow base). *)
  Lemma ash_ge : forall y, 0 <= y -> ASAN_K <= shadow_addr y.
  Proof. intros y Hy. unfold shadow_addr. pose proof (Z.div_pos y 8 Hy ltac:(lia)). unfold ASAN_K; lia. Qed.

  (* The side stack starts at or above ASAN_GT (fs_place of the fp invariant). *)
  Lemma alay_fs_gt : ASAN_GT <= FS.
  Proof.
    destruct FP as (DT_ & TS_ & C_ & T_ & DB_ & k_ & _ & _ & FSP & _ & _ & _ & _ & _ & _ & _).
    destruct FSP as (_ & _ & HGT & _ & _). exact HGT.
  Qed.

  (* An address below ASAN_GT (e.g. the read-only image blocks JOIN_0013 / JOIN_0014) is apart from the side
     stack's write set fp_w: the class bytes and frames start at or above FS >= ASAN_GT, their shadow at or above
     ASAN_K. *)
  Lemma ajoin_fpw : forall x, 0 <= x < ASAN_GT -> outside (fp_w [0%nat; 1%nat] FS) x.
  Proof.
    intros x Hx. pose proof alay_fs_gt as HGT. pose proof alay_fs as (HFpos & _ & _ & _).
    destruct (alay_fpw_bnd 0%nat (or_introl eq_refl)) as (H0a & _ & H0c & _ & H0e & _).
    destruct (alay_fpw_bnd 1%nat (or_intror eq_refl)) as (H1a & _ & H1c & _ & H1e & _).
    pose proof (ash_ge (fs_frame FS 0%nat 0) ltac:(lia)) as SH0.
    pose proof (ash_ge (fs_frame FS 1%nat 0) ltac:(lia)) as SH1.
    unfold ASAN_K in SH0, SH1. unfold ASAN_GT in HGT, Hx.
    cbn [fp_w flat_map fp_w1 outside].
    repeat split; try exact I; intros [C1 C2]; lia.
  Qed.

  (* A general shadow check (metadata byte k may be non-zero): `srli; add s11; lb` reads k, then `bnez` falls
     through when k = 0; else the slow path `andi a2, X, 7; blt` continues because X mod 8 < k, so the branch to
     the error path is not taken; either way the byte X is marked usable. *)
  Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.
  Ltac no_extra X := idtac.
  Ltac chk_go X r SH RS extra :=
    let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
    let RSh := fresh "RSh" in
    destruct SH as (k & RK & OK & KR); pose proof RS as RSh;
    step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
    step; step; clear RK RSh; steps_until_if;
    unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
    lazymatch goal with
    | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
        let G := fresh "G" in
        enough (G : forall rr : word, evtF segs RNG0 Q (MS (bvmap_set r rr R) F B fc rv mm ro));
        [ let K0 := fresh "K0" in
          destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
          [ bjoin G r
          | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; extra X;
            step;
            first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                      by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
                    replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia)
                  | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k))
                      by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
                    replace (X mod 8 + 3 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia) ];
            bjoin G r ]
        | intros ?; simp_regs; clear OK KR ]
    end.

  (* The em_fr trailer (0x85778 .. 0x857c8): s9 holds LEN, s0 holds o; the two checked trailing stores (194 at
     o + LEN - 2, -22 at o + LEN - 1), each preceded by its overflow guards whose branch to unimp at 0x85810 is
     not taken (o + LEN <= 2^64), then the epilogue via aepi. *)
  Lemma atail3 : forall (x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26
                        u3 u4 u5 u6 : word) (mc : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 BLK] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)) ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 LEN) x26 (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85778) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 u3 u4 u5 u6 mc jf
      HE FR ST MU WM MI AJ P1 P2 P3 P4 P5 P6 CLS.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (FpO HE) as FpOc.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_bytes rsegs mc (o + LEN + -2) 2 (repeat (Z_to_bv 8 0) 2) P6) as (_ & HB6 & HW6).
    clear P6.
    (* addi a0,s9,-2 ; add a0,a0,s0 : a0 = o + LEN - 2 *)
    do 2 step.
    replace (LEN + -2 + o) with (o + LEN + -2) by lia.
    (* beqz a0,85810 : not taken (o + LEN - 2 <> 0) *)
    step. unfold_cond. fold_lit_ux. rewrite (unsigned_lit (o + LEN + -2)) by lia.
    replace (o + LEN + -2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    (* bltu a0,s0,85810 : not taken (o <= o + LEN - 2) *)
    step. unfold_cond. rewrite (unsigned_lit (o + LEN + -2)) by lia. rewrite (unsigned_lit o) by lia.
    replace (o + LEN + -2 <? o) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    chk_go (o + LEN + -2) (Z_to_bv 5 12)
      (a_shadow mc o LEN (o + LEN + -2) (LEN - 2) AOm ltac:(lia) ltac:(lia)) (FpSo1 HE (o + LEN + -2) ltac:(lia)) no_extra.
    (* li a2,194 ; addi a1,s9,-1 ; not a3,s0 ; sb a2,0(a0) *)
    assert (HS1 : store_ok rsegs mc (wa (o + LEN + -2)) 1 = true).
    { pose proof (wr_at_store_ok rsegs mc (o + LEN + -2) (Z.of_nat 2) 0 1%nat HW6 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    step. step. step. step.
    replace (o + LEN + -2 + Z.of_nat 0) with (o + LEN + -2) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 194) by lia.
    assert (MU1 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m
                    (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM1 : wmono rsegs m (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply wmono_write; exact WM).
    assert (MI1 : mem_inv rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply mem_inv_store; [exact MI | cbn [length]; exact HS1]).
    assert (AJ1 : aJ (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply (aJ_ostore mc (o + LEN + -2) (Z_to_bv 8 194)); [exact AJ | exact API | exact ART | lia]).
    assert (FR1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR | lia | cbn [length]; lia
          | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST1 : stk rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) LO (SP0 + -128))
      by (apply stk_write; [exact ST | lia | cbn [length]; lia]).
    assert (HB1 : bytes_at rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + LEN + -2)
                    [Z_to_bv 8 194]) by (apply bytes_at_write_same; cbn [length]; lia).
    assert (HW1 : wr_at rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + LEN + -2) (Z.of_nat 2))
      by (apply wr_at_write; exact HW6).
    assert (P1_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P3_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 12) [CB 6 HDR])
      by (apply rw_cells_frame; [exact P3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P4_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 18) [CB 32 BLK])
      by (apply rw_cells_frame; [exact P4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P5_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 50)
                     [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply rw_cells_frame; [exact P5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    try fold (wa (o + LEN + -2)).
    set (m1 := write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) in *. clearbody m1.
    pose proof AJ1 as AJ1c. destruct AJ1c as (_ & _ & _ & AO1 & _ & _).
    (* bltu a3,a1,85810 (a3 = ~o, a1 = LEN - 1) : not taken (o + LEN - 1 < 2^64) *)
    step. unfold_cond. rewrite (unsigned_lit o) by lia. rewrite (zb_lxor_ones o) by lia.
    rewrite (unsigned_lit (18446744073709551615 - o)) by lia. rewrite (unsigned_lit (LEN + -1)) by lia.
    replace (18446744073709551615 - o <? LEN + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    (* add a0,s0,a1 : a0 = o + LEN - 1 *)
    step.
    replace (o + (LEN + -1)) with (o + LEN + -1) by lia.
    chk_go (o + LEN + -1) (Z_to_bv 5 12)
      (a_shadow m1 o LEN (o + LEN + -1) (LEN - 1) AO1 ltac:(lia) ltac:(lia)) (FpSo1 HE (o + LEN + -1) ltac:(lia)) no_extra.
    (* li a1,-22 ; sb a1,0(a0) *)
    assert (HS2 : store_ok rsegs m1 (wa (o + LEN + -1)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m1 (o + LEN + -2) (Z.of_nat 2) 1 1%nat HW1 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + LEN + -2 + 1) with (o + LEN + -1) in H by lia.
      exact H. }
    step. step.
    replace (o + LEN + -1 + Z.of_nat 0) with (o + LEN + -1) by lia.
    rewrite ?em_le1. rewrite em_byte_m22.
    assert (MU2 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m
                    (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply munch_write; [exact MU1 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM2 : wmono rsegs m (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply mem_inv_store; [exact MI1 | cbn [length]; exact HS2]).
    assert (AJ2 : aJ (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply (aJ_ostore m1 (o + LEN + -1) (Z_to_bv 8 234)); [exact AJ1 | exact API | exact ART | lia]).
    assert (FR2 : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR1 | lia | cbn [length]; lia
          | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST2 : stk rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) LO (SP0 + -128))
      by (apply stk_write; [exact ST1 | lia | cbn [length]; lia]).
    assert (HBF : bytes_at rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + LEN + -2)
                    [Z_to_bv 8 194; Z_to_bv 8 234]).
    { change [Z_to_bv 8 194; Z_to_bv 8 234] with ([Z_to_bv 8 194] ++ [Z_to_bv 8 234]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + LEN + -2 + Z.of_nat 1) with (o + LEN + -1) by lia.
        apply bytes_at_write_same; cbn [length]; lia. }
    assert (P1' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P3' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 12) [CB 6 HDR])
      by (apply rw_cells_frame; [exact P3_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P4' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 18) [CB 32 BLK])
      by (apply rw_cells_frame; [exact P4_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P5' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply rw_cells_frame; [exact P5_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    try fold (wa (o + LEN + -1)).
    set (m2 := write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) in *.
    assert (RReq : (if EE then LEN else 0) = LEN) by (rewrite HE; reflexivity).
    pose proof AJ2 as AJ2c. destruct AJ2c as (AC2 & SW2 & AW2 & AO2 & FP2 & TL2).
    eapply aepi.
    - symmetry; exact RReq.
    - lia.
    - exact FR2.
    - exact ST2.
    - rewrite RReq. exact MU2.
    - exact WM2.
    - exact MI2.
    - exact AC2.
    - exact SW2.
    - exact AW2.
    - rewrite RReq. exact FP2.
    - intros _. unfold aRES. split; [|split].
      + exact (em_fr_bytes rsegs m2 o LEN db sb BLK (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0))
                 (nth 1 row (Z_to_bv 8 0)) P1' P2' P3' P4' P5' HBF ltac:(lia)).
      + intros HL2. exact (em_E_wok _ _ _ _ HE HL2).
      + exact CLS.
  Qed.

  (* The ctrl_finish call (0x8576c .. 0x85778): stamps the block (o + 18, o + 50), keeping t2 and the callee-saved
     registers; then the em_fr trailer via atail3. The callee's side-stack frame is 32 bytes. *)
  Lemma atail2 : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26
                        u3 u4 u5 u6 : word) (mc : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    bytes_at rsegs mc f row -> addressable mc (f + 18) 3 ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 LB] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 LEN) x26 (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8576c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 u3 u4 u5 u6 mc jf
      HE FR ST MU WM MI AJ HRf ADf3 P1 P2 P3 P4 P5 P6.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    pose proof Dsf as Dsfu. unfold ly_dj in Dsfu.
    pose proof FPm as FPm2. destruct FPm2 as (DT & TS & C & T & DB & kk & _ & _ & _ & _ & _ & _ & FSlo & _).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as R18.
    pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as R20.
    assert (Hrn : 0 <= RO) by (unfold ubat; lia).
    assert (Hcn : 0 <= CC <= 2) by (unfold ubat in Hc |- *; lia).
    (* mv a0,s0 ; mv a1,s1 ; jal ctrl_finish *)
    step. step. step.
    eapply evtF_cut.
    { eapply HFN with (p := o) (f := f) (c := CC) (o := RO) (n := RL) (lo := LO) (row := row) (B := LB).
      - reflexivity.
      - reflexivity.
      - exact Hf8.
      - exact Hf24.
      - exact Hrl.
      - exact HRf.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Hc.
      - exact Hc2.
      - exact Ho.
      - lia.
      - intros _; exact P4.
      - rewrite Esp; exact ST.
      - rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - rewrite Esp; lia.
      - intros _; rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - exact ACm.
      - exact SWm.
      - exact ADf3.
      - intros _; exact (addressable_sub mc o LEN 18 32 AOm ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros x Hx. rewrite Esp. cbn [outside]. split.
        + unfold RT_LO, RT_HI, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
            CTRL_FINISH_FRAME in Hx, FSlo |- *; unfold HIGHMEM_BEG in HHM.
          destruct Hx as [HRt|HSt]; lia.
        + apply (em_fin_sub CC RO RL o Hc Hrn Hc2). cbn [outside]. split; [|exact I].
          destruct Hx as [HRt|HSt].
          * unfold RT_LO, RT_HI in ART, HRt |- *; lia.
          * pose proof (app_ivl_meta o (o + LEN) x API HSt) as Hm2; lia.
      (* the footprint premises of ctrl_finish_contract_F *)
      - rewrite Esp. eapply rng_sub; [exact FpWIN | unfold CTRL_FINISH_FRAME; lia | unfold CTRL_FINISH_FRAME; lia].
      - eapply rng_sub; [exact FpIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia].
      - exact FpROW.
      - exact (dcF_shadowspan RNG ASAN_K f (f + 23) (f + 18) (f + 20)
                 (FpSfK f (f + 23) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros _. split.
        + eapply rng_sub; [exact (FpO HE) | lia | lia].
        + exact (dcF_shadowspan RNG ASAN_K o (o + LEN - 1) (o + 18) (o + 49)
                   (FpSoK HE o (o + LEN - 1) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' (t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & -> & MU1 & WM1 & MI1 & ST1 & HF).
    fixret. rewrite Esp in MU1, ST1.
    pose proof (MI1 MI) as MIm1.
    assert (SUBw : sub_fp ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o) aWL).
    { intros x Hx. apply (em_fin_sub2 CC RO RL o (SP0 + -128 - 32, SP0 + -128) Hc Hrn Hc2).
      cbn [outside] in Hx |- *. destruct Hx as (HAx & HBx & _). split; [lia | split; [lia | exact I]]. }
    assert (MU1' : munch [(SP0 + -128 - 32, SP0 + -128); (o + 18, o + 50)] mc m1)
      by (apply (munch_weaken _ _ mc m1 (em_fin_sub2 CC RO RL o (SP0 + -128 - 32, SP0 + -128) Hc Hrn Hc2)); exact MU1).
    assert (MUf : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m1).
    { apply (munch_trans _ m mc m1 MU).
      apply (munch_weaken ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
      intros x Hx. apply SUBw. cbn [outside app] in Hx |- *. tauto. }
    assert (WMf : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc m1 WM WM1)).
    assert (AJm1 : aJ m1).
    { apply (aJ_wout ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o) mc m1 API ART AJ MU1 WM1 SUBw).
      intros x Hx. assert (xLO : x < LO) by lia.
      destruct (Z.eq_dec CC 0) as [C0|C0].
      - left. rewrite C0. cbn [fin_w outside]. split; [lia | exact I].
      - destruct (Z_lt_le_dec x (o + 18)) as [L1|L1].
        + left. cbn [outside]. split;
            [lia | apply (em_fin_sub CC RO RL o Hc Hrn Hc2); cbn [outside]; split; [lia | exact I]].
        + destruct (Z_lt_le_dec x (o + 50)) as [L2|L2].
          * right. destruct (HF ltac:(lia)) as (HB4 & _ & _).
            destruct (em_rw_bytes rsegs m1 (o + 18) 32 (fin CC RO RL LB) HB4) as (HL4 & (_ & _ & HBf) & _).
            pose proof (HBf (Z.to_nat (x - (o + 18)))) as HM4. rewrite HL4 in HM4.
            specialize (HM4 ltac:(lia)).
            replace (o + 18 + Z.of_nat (Z.to_nat (x - (o + 18)))) with x in HM4 by lia.
            destruct (nth_error (fin CC RO RL LB) (Z.to_nat (x - (o + 18)))) as [b|] eqn:EN.
            -- exists b. exact HM4.
            -- apply nth_error_None in EN. rewrite HL4 in EN. lia.
          * left. cbn [outside]. split;
              [lia | apply (em_fin_sub CC RO RL o Hc Hrn Hc2); cbn [outside]; split; [lia | exact I]]. }
    assert (FRm1 : rw_cells rsegs m1 (SP0 + -128)
                     [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                      C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1' WM1);
          cbn [disjoint_from cells_size csize Nat.add length]; lia).
    assert (P1' : rw_cells rsegs m1 o [CB 6 db])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P1 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P2' : rw_cells rsegs m1 (o + 6) [CB 6 sb])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P2 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P3' : rw_cells rsegs m1 (o + 12) [CB 6 HDR])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P3 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P5' : rw_cells rsegs m1 (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P5 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P6' : rw_cells rsegs m1 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P6 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P4' : rw_cells rsegs m1 (o + 18) [CB 32 BLK]).
    { destruct (Z.eq_dec CC 0) as [C0|C0].
      - assert (BLKeq : BLK = LB) by (unfold fin; rewrite C0; reflexivity).
        rewrite BLKeq.
        assert (MUw : munch [(SP0 + -128 - 32, SP0 + -128)] mc m1).
        { apply (munch_weaken ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
          rewrite C0. cbn [fin_w]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
        apply (rw_cells_transport rsegs [(SP0 + -128 - 32, SP0 + -128)] mc m1 _ _ P4 MUw WM1);
          cbn [disjoint_from cells_size csize]; lia.
      - destruct (HF ltac:(lia)) as (HB4 & _ & _). exact HB4. }
    assert (CLS' : CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).
    { intros HCC. destruct (HF HCC) as (_ & CL1 & CL2). split; [exact CL1 | exact CL2]. }
    eapply (atail3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 jf);
      [ exact HE | exact FRm1 | exact ST1 | exact MUf | exact WMf | exact MIm1 | exact AJm1
      | exact P1' | exact P2' | exact P3' | exact P4' | exact P5' | exact P6' | exact CLS' ].
  Qed.

  (* lia with one apartness fact (ly_dj) unfolded locally: the context keeps the others folded, so em_lia does
     not split cases on them. *)
  Local Ltac djl H := let X := fresh "X" in pose proof H as X; unfold ly_dj in X; lia.

  (* sub_fp of the ctrl_lay_block post window aWlay inside the function-wide window. *)
  Lemma alay_sub_wlay : EE = true ->
    sub_fp aWlay (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]).
  Proof.
    intros HE x Hx. pose proof (em_len_rng _ _ _ _ HE) as RLN. pose proof arng_sp as Rsp.
    cbn [outside app] in Hx. destruct Hx as (Hlo & Ho_ & Hrest).
    destruct (alay_oai (fp_w [0%nat; 1%nat] FS) [(shadow_addr LO, shadow_addr SP0)] x Hrest) as (Hfpw_x & HY_x).
    cbn [outside] in HY_x. destruct HY_x as (HYx & _).
    apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [|split; [|exact I]].
      + intros [A1 A2]. apply Ho_; lia.
      + intros [A1 A2]. apply Hlo; unfold CTRL_LAY_BLOCK_K in *; lia.
    - exact Hfpw_x.
    - cbn [outside]. split; [|exact I]. intros [A1 A2]. apply HYx. split.
      + replace (shadow_addr LO) with (shadow_addr (SP0 + -128 - CTRL_LAY_BLOCK_K));
          [exact A1 | f_equal; unfold CTRL_LAY_BLOCK_K; lia].
      + pose proof (alay_shge SP0 (SP0 + -128) ltac:(lia)) as G. lia.
  Qed.

  (* disjoint_from distributes over list concatenation. *)
  Lemma adj_app : forall (A B : list ivl) a sz,
    disjoint_from A a sz -> disjoint_from B a sz -> disjoint_from (A ++ B) a sz.
  Proof.
    induction A as [|[lo hi] A IH]; intros B a sz HdA HdB; [exact HdB|].
    cbn [app disjoint_from] in *. destruct HdA as [Hd HdA]. split; [exact Hd | apply IH; assumption].
  Qed.

  (* A single range apart from W (fp_dj) is disjoint_from W. *)
  Lemma adj_of_fpdj : forall W A sz, fp_dj [(A, A + sz)] W -> disjoint_from W A sz.
  Proof.
    intros W A sz H. unfold fp_dj in H. apply Forall_inv in H. cbn [fst snd] in H.
    induction W as [|[lo hi] W IH]; cbn [disjoint_from]; [exact I|].
    apply Forall_cons_iff in H as [Hd Hw]. cbn [fst snd] in Hd. unfold ly_dj in Hd.
    split; [exact Hd | exact (IH Hw)].
  Qed.

  (* A region at or above the window base [LO, ...) is disjoint from the side stack's write set (which lies below
     LO, and whose frame shadow lies below LO too). *)
  Lemma adj_fpw_hi : forall A sz, LO <= A -> disjoint_from (fp_w [0%nat; 1%nat] FS) A sz.
  Proof.
    intros A sz HAl. pose proof alay_fs as (FSpos & Fmod & Fapp & FSL). pose proof arng_sp as Rsp.
    destruct (alay_fpw_bnd 0%nat (or_introl eq_refl)) as (H0a & H0b & H0c & H0d & H0e & H0f).
    destruct (alay_fpw_bnd 1%nat (or_intror eq_refl)) as (H1a & H1b & H1c & H1d & H1e & H1f).
    assert (SHLO : shadow_addr LO < LO) by (unfold shadow_addr, ASAN_K; unfold HIGHMEM_BEG in HHM; rlia).
    pose proof (alay_shge LO (fs_frame FS 0%nat (fs_M 0%nat)) ltac:(lia)) as SG0.
    pose proof (alay_shge LO (fs_frame FS 1%nat (fs_M 1%nat)) ltac:(lia)) as SG1.
    cbn [fp_w flat_map fp_w1 disjoint_from]. repeat split; try exact I; right; lia.
  Qed.

  (* An application-memory region is disjoint from the shadow of any two application addresses a <= b. *)
  Lemma adj_sh_out : forall A sz a b, (A + sz <= LOWMEM_END \/ HIGHMEM_BEG <= A) -> app_mem a -> app_mem b ->
    disjoint_from [(shadow_addr a, shadow_addr b)] A sz.
  Proof.
    intros A sz a b Hcase Ha Hb.
    pose proof (shadow_of_app a Ha) as Sa. pose proof (shadow_of_app b Hb) as Sb.
    cbn [disjoint_from]. split; [|exact I].
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Sa, Sb.
    unfold LOWMEM_END, HIGHMEM_BEG in Hcase. destruct Hcase; [left | right]; lia.
  Qed.

  (* An application interval lies on one side of the gap between low and high memory. *)
  Lemma alay_ivl_side : forall lo hi, app_ivl lo hi -> lo < hi -> hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
  Proof.
    intros lo hi H Hlt. destruct (Z_lt_le_dec lo LOWMEM_END) as [L|L].
    - destruct (Z_le_gt_dec hi LOWMEM_END) as [L2|L2]; [left; exact L2|].
      exfalso. pose proof (H LOWMEM_END ltac:(lia)) as Hm. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in *. lia.
    - right. pose proof (H lo ltac:(lia)) as Hm. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in *. lia.
  Qed.

  (* One range of an apart list is apart. *)
  Lemma alay_dj_in : forall L X a b, fp_dj L X -> In (a, b) L -> fp_dj [(a, b)] X.
  Proof.
    intros L X a b H Hin. unfold fp_dj in *. rewrite Forall_forall in H.
    constructor; [exact (H _ Hin) | constructor].
  Qed.

  (* A piece [A, A + sz) of the output apart from the block [o + 18, o + 50) is apart from the ctrl_lay_block
     call's writes aWlay. *)
  Lemma alay_dj_out : forall A sz, EE = true -> 0 <= sz -> o <= A -> A + sz <= o + LEN ->
    (A + sz <= o + 18 \/ o + 50 <= A) -> fp_dj aDL (fp_w [0%nat; 1%nat] FS) -> disjoint_from aWlay A sz.
  Proof.
    intros A sz HE Hsz H1 H2 H3 HDd.
    pose proof (em_len_rng _ _ _ _ HE) as RLN. pose proof arng_sp as Rsp.
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    destruct (AO HE) as (AOo & _ & _).
    pose proof (addressable_app m o LEN AOo) as AIo.
    pose proof (addressable_app m LO 4640 AWIN) as AIw.
    apply adj_app; [| apply adj_app].
    - cbn [disjoint_from]. split; [lia | split; [unfold CTRL_LAY_BLOCK_K; lia | exact I]].
    - apply adj_of_fpdj. apply (fl_dj_sub o (o + LEN) A (A + sz)); [| lia | lia | lia].
      exact (alay_dj_in aDL _ o (o + LEN) HDd ltac:(cbn [In]; right; right; right; right; left; reflexivity)).
    - apply adj_sh_out.
      + pose proof (alay_ivl_side o (o + LEN) AIo ltac:(lia)) as S. lia.
      + unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. apply AIw; lia.
      + apply AIw; lia.
  Qed.

  (* The frame [SP0 + -128, SP0) is apart from the ctrl_lay_block call's writes aWlay. *)
  Lemma alay_dj_fr : forall sz, EE = true -> sz = 128 -> disjoint_from aWlay (SP0 + -128) sz.
  Proof.
    intros sz HE ->. pose proof (em_len_rng _ _ _ _ HE) as RLN. pose proof arng_sp as Rsp.
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    pose proof (addressable_app m LO 4640 AWIN) as AIw.
    apply adj_app; [| apply adj_app].
    - cbn [disjoint_from]. split; [lia | split; [unfold CTRL_LAY_BLOCK_K; lia | exact I]].
    - apply adj_fpw_hi. lia.
    - apply adj_sh_out.
      + right. lia.
      + unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. apply AIw; lia.
      + apply AIw; lia.
  Qed.

  (* E3 of the glue draft, first half: 0x8571c .. the jal at 0x8572c.  The ctrl_lay_block argument setup and the
     call, ending at the callee's entry 0x86104 with ra = 0x85730 and the memory unchanged.  It holds no cut, so a
     caller can put the callee's contract (or its own run of it) in its place. *)
  Lemma alay_pre : forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word)
      (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    evtF rsegs RNG
      (fun ms' => ms' =
         MS (mkR (Z_to_bv 64 0x85730) (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f)
                 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g) x14 x15 x16 x17
                 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
                 (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
                 (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
            F (Z_to_bv 64 0x86104) fc None mc (seg_rom rsegs))
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 mc HE FR ST.
    pose proof arng_sp as Rsp.
    (* read the three spill slots as cells *)
    apply arw_cb3 in FR.
    (* 0x8571c: mv a0,s0; mv a1,s1; mv a2,s6; ld a3,8(sp); jal ctrl_lay_block *)
    do 5 step.
    apply evtF_done. reflexivity.
  Qed.

  (* E3 of the glue draft, second half: 0x85730 (ctrl_lay_block's return) .. the ctrl_finish trailer.  The s2
     row[23] check and, when row[23] = 1, the reac_braid_encode call; then atail2.  The facts the block reads at
     0x85730 are premises, so the lemma never mentions ctrl_lay_block or its fake-stack footprint.  The proof text
     is the one alay_call carried. *)
  Lemma alay_ret : forall (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w0 : word)
      (m1 : word -> option byte),
    EE = true ->
    rw_cells rsegs m1 (SP0 + -128)
      (C8 w0 :: C8 (Z_to_bv 64 g) :: C8 (Z_to_bv 64 ns) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs m1 LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 -> aJ m1 ->
    bytes_at rsegs m1 f row -> addressable m1 f 24 ->
    rw_cells rsegs m1 o [CB 6 db] -> rw_cells rsegs m1 (o + 6) [CB 6 sb] ->
    rw_cells rsegs m1 (o + 12) [CB 6 HDR] -> rw_cells rsegs m1 (o + 18) [CB 32 LB] ->
    rw_cells rsegs m1 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs m1 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp t0' t1' t2'
               (Z_to_bv 64 o) (Z_to_bv 64 f) a0' a1' a2' a3' a4' a5' a6' a7'
               (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) t3' t4' t5' t6')
          F (Z_to_bv 64 0x85730) fc None m1 (seg_rom rsegs)).
  Proof.
    intros x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w0 m1
      HE FR1 ST1 MUtot WMtot MIm1 AJ1 HRf1 Af1 P1' P2' P3' LAY P5' P6'.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof Af as Afb. destruct Afb as (Hfge & _ & _ & _).
    pose proof Amd as Amdb. destruct Amdb as (Hmdge & _ & _ & _).
    pose proof AJ1 as AJ1c. destruct AJ1c as (ACm1 & SWm1 & AWm1 & AOm1 & FPm1 & TLm1).
    pose proof (addressable_app m1 o LEN AOm1) as AIo.
    destruct (AO HE) as (AOaddr & AOend & ART).
    destruct (HEo HE) as (HOrw & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (ADf3 : addressable m1 (f + 18) 3)
      by (exact (addressable_sub m1 f 24 18 3 Af1 ltac:(lia) ltac:(lia) ltac:(lia))).
    (* 0x85730: addi a0,s1,23 ; the checked read of row[23] (the byte f + 23 is in the addressable row) *)
    pose proof (rd_byte rsegs m1 f row 23 HRf1 ltac:(lia)) as RD23. change (Z.of_nat 23) with 23 in RD23.
    pose proof (byte_range (nth 23 row (Z_to_bv 8 0))) as R23.
    step.
    chk_go (f + 23) (Z_to_bv 5 12) (a_shadow m1 f 24 (f + 23) 23 Af1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 23) ltac:(lia)) no_extra.
    (* lbu a0,0(a0) ; ld a4,16(sp) ; beqz a0,0x8576c *)
    step. step. step.
    rewrite (rc_u8_eqb row 23 0) by lia.
    pose proof (rc_u8_range row 23) as R23u.
    destruct (Z.eqb_spec (rc_u8 row 23) 0) as [A0|A0]; cbv iota.
    - (* row[23] = 0: straight to the ctrl_finish call *)
      eapply atail2 with (mc := m1) (jf := le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns));
        [ exact HE | exact (arw_cb3' m1 _ _ _ _ _ FR1) | exact ST1 | exact MUtot | exact WMtot | exact MIm1
        | exact AJ1 | exact HRf1 | exact ADf3 | exact P1' | exact P2' | exact P3' | exact LAY | exact P5'
        | exact P6' ].
    - (* row[23] = 1: the guard (o < 2^64 - 50), then reac_braid_encode(o + 50, n, w0, n, ns) with ns <= 0 *)
      assert (A1 : AA = 1) by (pose proof HA as HA'; unfold ubat in HA' |- *; unfold rc_u8 in A0, R23u; lia).
      step. step. unfold_cond. rewrite (unsigned_lit o) by lia.
      change (bv_unsigned (Z_to_bv 64 (-50))) with 18446744073709551566.
      replace (o <? 18446744073709551566) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
      do 5 step.
      eapply evtF_cut.
      { eapply HBR with (ns := ns); [pose proof (Hns0 A1); lia | reflexivity | |].
        - rewrite Esp. unfold REAC_BRAID_ENCODE_FRAME.
          destruct (stk_split rsegs m1 LO (SP0 + -128 - 128) (SP0 + -128) ST1 ltac:(lia)) as (_ & STb).
          exact STb.
        - rewrite Esp. unfold REAC_BRAID_ENCODE_FRAME. eapply rng_sub; [exact FpWIN | lia | lia]. }
      intros ms' (m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite Esp in MU2, ST2. unfold REAC_BRAID_ENCODE_FRAME in MU2, ST2.
      fixret.
      assert (WB : sub_fp [(SP0 + -128 - 128, SP0 + -128)] [(LO, SP0)])
        by (intros x Hx; cbn [outside] in *; destruct Hx as [H1 _]; split; [lia | exact I]).
      assert (AJ2 : aJ m2) by (exact (aJ_win _ m1 m2 AJ1 MU2 WM2 WB)).
      assert (MUtot2 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m2).
      { apply (munch_trans _ m m1 m2 MUtot).
        apply (munch_weaken [(SP0 + -128 - 128, SP0 + -128)]); [|exact MU2].
        intros x Hx. cbn [outside app] in Hx. destruct Hx as (H1 & _). cbn [outside]. split; [lia | exact I]. }
      assert (WMtot2 : wmono rsegs m m2) by (exact (wmono_trans rsegs m m1 m2 WMtot WM2)).
      pose proof (MI2 MIm1) as MIm2.
      assert (ST2' : stk rsegs m2 LO (SP0 + -128)).
      { destruct (stk_split rsegs m1 LO (SP0 + -128 - 128) (SP0 + -128) ST1 ltac:(lia)) as (STa & _).
        pose proof (stk_transport_disjoint rsegs _ m1 m2 LO (SP0 + -128 - 128) STa MU2 WM2
                      ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STa2.
        exact (stk_merge rsegs m2 LO (SP0 + -128 - 128) (SP0 + -128) STa2 ST2 ltac:(lia)). }
      assert (FR2 : rw_cells rsegs m2 (SP0 + -128)
                      (C8 w0 :: C8 (Z_to_bv 64 g) :: C8 (Z_to_bv 64 ns) ::
                       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
                       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]))
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2);
            cbn [disjoint_from cells_size csize Nat.add length]; lia).
      assert (P1'' : rw_cells rsegs m2 o [CB 6 db])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P1' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P2'' : rw_cells rsegs m2 (o + 6) [CB 6 sb])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P2' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P3'' : rw_cells rsegs m2 (o + 12) [CB 6 HDR])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P3' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P4'' : rw_cells rsegs m2 (o + 18) [CB 32 LB])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ LAY MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P5'' : rw_cells rsegs m2 (o + 50)
                       [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P5' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P6'' : rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P6' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (HRf2 : bytes_at rsegs m2 f row)
        by (apply (bytes_at_transport rsegs _ m1 m2 f row HRf1 MU2); rewrite Hrl;
            cbn [disjoint_from]; split; [djl Dsf | exact I]).
      assert (ADf3' : addressable m2 (f + 18) 3)
        by (exact (fl_addressable _ m1 m2 (f + 18) 3 ADf3 MU2 (fun x Hx => fl_shadow_out _ LO SP0 x WB HHM Hx))).
      eapply atail2 with (mc := m2) (jf := le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns));
        [ exact HE | exact (arw_cb3' m2 _ _ _ _ _ FR2) | exact ST2' | exact MUtot2 | exact WMtot2 | exact MIm2
        | exact AJ2 | exact HRf2 | exact ADf3' | exact P1'' | exact P2'' | exact P3'' | exact P4'' | exact P5''
        | exact P6'' ].
  Qed.

  (* The ctrl_lay_block call segment (0x8571c .. 0x8576c): the arg setup, the call (ly_lay written to [o + 18,
     o + 50)), the s2 row[23] check (the branch to the error path is not taken because the byte is marked usable),
     and, when row[23] <> 0, the reac_braid_encode call; then the ctrl_finish trailer via atail2. *)
  Lemma alay_call : forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word)
      (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    bytes_at rsegs mc (o + 12) HDR -> wr_at rsegs mc (o + 12) (Z.of_nat 6) ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    evtF rsegs RNG aQp
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 mc
      HE FR ST MU WM MI AJ P1 P2 PH12 HW12 P18.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as AIo.
    destruct (AO HE) as (AOaddr & AOend & ART).
    destruct (HEo HE) as (HOrw & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    pose proof FPm as FPd.
    destruct FPd as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    pose proof Af as Afb. destruct Afb as (Hfge & _ & _ & _).
    pose proof Amd as Amdb. destruct Amdb as (Hmdge & _ & _ & _).
    assert (AIf : app_ivl f (f + 24)) by (exact (addressable_app m f 24 Af)).
    assert (Hfpwf : forall x, f <= x < f + 24 -> outside (fp_w [0%nat; 1%nat] FS) x)
      by (intros x Hx; exact (fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) f (f + 24) x HDd
              ltac:(cbn [In]; left; reflexivity) Hx)).
    assert (Afmc : addressable mc f 24)
      by (exact (akeep_addr f 24 mc Af AIf AIo ltac:(djl Dsf) Hfpwf MU)).
    (* split the output tail [o + 18, o + LEN) into the block and the trailing pieces *)
    destruct (em_rw_rep rsegs mc (o + 18) (Z_to_bv 8 0) (Z.to_nat (LEN - 18)) 32 P18 ltac:(lia)) as (Pblk & Prest).
    replace (o + 18 + Z.of_nat 32) with (o + 50) in Prest by lia.
    replace (Z.to_nat (LEN - 18) - 32)%nat with (Z.to_nat (LEN - 50)) in Prest by lia.
    destruct (em_rw_rep rsegs mc (o + 50) (Z_to_bv 8 0) (Z.to_nat (LEN - 50)) (Z.to_nat (LEN - 52)) Prest
                ltac:(lia)) as (P50 & Pend).
    replace (o + 50 + Z.of_nat (Z.to_nat (LEN - 52))) with (o + LEN + -2) in Pend by lia.
    replace (Z.to_nat (LEN - 50) - Z.to_nat (LEN - 52))%nat with 2%nat in Pend by lia.
    (* 0x8571c .. the jal: alay_pre (E3); the frame cells are then read as C8 for the block below *)
    pose proof FR as FR0.
    apply arw_cb3 in FR.
    eapply evtF_cut;
      [ exact (alay_pre x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 mc HE FR0 ST) |].
    intros ms0 ->.
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply HLB with (p := o) (f := f) (md := md) (g := g) (fr := row) (ob := repeat (Z_to_bv 8 0) 32)
                      (tb := tb) (mb := mb) (nb := nb) (gb := gb).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact Hg.
      - rewrite Esp. rlia.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. exact ST.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K. apply (em_dj_sub _ _ _ _ _ _ _ _ DsoLO); lia.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K. apply (em_dj_sub _ _ _ _ _ _ _ _ Dsf); lia.
      - intros Hk2. rewrite Esp. unfold CTRL_LAY_BLOCK_K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dst Hk2)); lia.
      - intros G0 A0. rewrite Esp. unfold CTRL_LAY_BLOCK_K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsg G0 A0)); lia.
      - intros Hk39 Hmd. rewrite Esp. unfold CTRL_LAY_BLOCK_K. split.
        + apply (em_dj_sub _ _ _ _ _ _ _ _ Dsm); lia.
        + intros Hbb Hhas Hrn.
          apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsn (conj (conj Hk39 Hbb) (conj Hhas Hrn)))); lia.
      - exact Hf8.
      - exact Hf24.
      - exact Hrl.
      - exact (akeep_bytes f 24 row mc HR ltac:(rewrite Hrl; reflexivity) AIf ltac:(djl Dsf) ltac:(djl Dof) Hfpwf MU).
      - exact Hk.
      - exact Hao.
      - exact Htm.
      - lia.
      - lia.
      - exact Pblk.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dof); lia.
      - intros Hk2. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dot Hk2)); lia.
      - intros Hk39 Hmd. apply (em_dj_sub _ _ _ _ _ _ _ _ Dom); lia.
      - intros Hk39 Hmd Hbb Hhas Hrn.
        apply (em_dj_sub _ _ _ _ _ _ _ _ (Don (conj (conj Hk39 Hbb) (conj Hhas Hrn)))); lia.
      - intros Hk39 Hmd. split; [exact Hmd8|]. split; [exact Hml|]. split.
        + exact (akeep_bytes md 296 mb mc HM ltac:(rewrite Hml; reflexivity)
                   (addressable_app m md 296 Amd) ltac:(djl Dsm) ltac:(djl Dom)
                   (fun x Hx => fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) md (md + 296) x HDd
                      ltac:(cbn [In]; right; left; reflexivity) Hx) MU).
        + intros Hbb Hhas Hrn. pose proof (conj (conj Hk39 Hbb) (conj Hhas Hrn)) as NMc.
          destruct (Hnm NMc) as (NO & NB). split; [exact NO|].
          exact (akeep_bytes (rname mb) (Z.of_nat (length nb)) nb mc NB eq_refl
                   (addressable_app m (rname mb) (Z.of_nat (length nb)) (An NMc))
                   ltac:(djl (Dsn NMc))
                   ltac:(djl (Don NMc))
                   (fun x Hx => fl_dj_out_r [(rname mb, rname mb + Z.of_nat (length nb))]
                      (fp_w [0%nat; 1%nat] FS) (rname mb) (rname mb + Z.of_nat (length nb)) x (FPn NMc)
                      ltac:(cbn [In]; left; reflexivity) Hx) MU).
      - intros G0 A0. destruct (Hgb G0 A0) as (GL & GB). split; [exact GL|]. split.
        + exact (akeep_bytes g (ly_al row) gb mc GB GL (addressable_app m g (ly_al row) (Ag G0 A0))
                   ltac:(djl (Dsg G0 A0))
                   ltac:(djl (Dog G0 A0))
                   (fun x Hx => fl_dj_out_r [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS) g (g + ly_al row) x
                      (FPg G0 A0) ltac:(cbn [In]; left; reflexivity) Hx) MU).
        + apply (em_dj_sub _ _ _ _ _ _ _ _ (Dog G0 A0)); lia.
      - exact MI.
      - exact ACm.
      - exact SWm.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. exact HHM.
      - rewrite Esp. lia.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with (LO + 0) by lia.
        apply (addressable_sub mc LO 4640 0 4512 AWm); lia.
      - exact Afmc.
      - exact (addressable_sub mc o LEN 18 32 AOm ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact (AIo (o + 50) ltac:(lia)).
      - lia.
      - intros Hk2. exact (akeep_addr (ly_tm row) 32 mc (Atm Hk2)
          (addressable_app m (ly_tm row) 32 (Atm Hk2)) AIo
          ltac:(djl (Dst Hk2))
          (fun x Hx => fl_dj_out_r [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS)
             (ly_tm row) (ly_tm row + 32) x (FPtm Hk2) ltac:(cbn [In]; left; reflexivity) Hx) MU).
      - intros G0 A0. split; [|split; [|split]].
        + exact (akeep_addr g (ly_al row) mc (Ag G0 A0) (addressable_app m g (ly_al row) (Ag G0 A0)) AIo
            ltac:(djl (Dsg G0 A0))
            (fun x Hx => fl_dj_out_r [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS) g (g + ly_al row) x
               (FPg G0 A0) ltac:(cbn [In]; left; reflexivity) Hx) MU).
        + exact (proj1 (APg G0 A0)).
        + exact (proj2 (APg G0 A0)).
        + exact (AIo (o + 25 + ly_ao row) ltac:(pose proof (rc_u8_range row 16) as R16;
            pose proof (rc_u8_range row 17) as R17; change (rc_u8 row 16) with (ly_ao row) in R16;
            change (rc_u8 row 17) with (ly_al row) in R17; lia)).
      - intros Hk39 Hmd. split.
        + exact (akeep_addr md 296 mc Amd (addressable_app m md 296 Amd) AIo ltac:(djl Dsm)
            (fun x Hx => fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) md (md + 296) x HDd
               ltac:(cbn [In]; right; left; reflexivity) Hx) MU).
        + intros Hbb Hhas Hrn. pose proof (conj (conj Hk39 Hbb) (conj Hhas Hrn)) as NMc.
          exact (akeep_addr (rname mb) (Z.of_nat (length nb)) mc (An NMc)
            (addressable_app m (rname mb) (Z.of_nat (length nb)) (An NMc)) AIo
            ltac:(djl (Dsn NMc))
            (fun x Hx => fl_dj_out_r [(rname mb, rname mb + Z.of_nat (length nb))]
               (fp_w [0%nat; 1%nat] FS) (rname mb) (rname mb + Z.of_nat (length nb)) x (FPn NMc)
               ltac:(cbn [In]; left; reflexivity) Hx) MU).
      - intros Hk5. exact (akeep_addr JOIN_0014 32 mc (AJ14 Hk5)
          (addressable_app m JOIN_0014 32 (AJ14 Hk5)) AIo
          ltac:(unfold JOIN_0014, LOWMEM_END, HIGHMEM_BEG in *; lia)
          (fun x Hx => ajoin_fpw x ltac:(unfold JOIN_0014, ASAN_GT in *; lia)) MU).
      - intros Hk6. exact (akeep_addr JOIN_0013 32 mc (AJ13 Hk6)
          (addressable_app m JOIN_0013 32 (AJ13 Hk6)) AIo
          ltac:(unfold JOIN_0013, LOWMEM_END, HIGHMEM_BEG in *; lia)
          (fun x Hx => ajoin_fpw x ltac:(unfold JOIN_0013, ASAN_GT in *; lia)) MU).
      - rewrite Esp. exact (alay_fp mc ltac:(lia) FPm).
      - exact FPtm.
      - exact FPg.
      - intros Hk39 Hmd. split.
        + unfold fp_dj in HDd |- *. apply Forall_forall. intros w Hw. cbn [In] in Hw.
          destruct Hw as [E|[]]. subst w. rewrite Forall_forall in HDd.
          exact (HDd (md, md + 296) ltac:(cbn [In]; right; left; reflexivity)).
        + intros Hbb Hhas Hrn. exact (FPn (conj (conj Hk39 Hbb) (conj Hhas Hrn))).
      - rewrite Esp. exact (alay_tls mc TLm).
      (* the footprint premises of ctrl_lay_block_contract_F *)
      - exact FpRB.
      - exact FpIMG.
      - eapply rng_sub; [exact FpIMG | unfold RT_LO | unfold RT_LO, RT_HI]; lia.
      - rewrite Esp. unfold CTRL_LAY_BLOCK_K.
        eapply rng_sub; [exact FpWIN | lia | lia].
      - rewrite Esp.
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr,
          CTRL_LAY_BLOCK_K.
        exact (FpWSH (SP0 + -128 - 4512) (SP0 + -128 - 4512 + 4512 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact (proj1 (tp_rng_of_rng_tls _ _ _ _ _ _ _ _ _ FP FpTLS)).
      - exact (proj2 (tp_rng_of_rng_tls _ _ _ _ _ _ _ _ _ FP FpTLS)).
      - apply tls_rng_of_rng_tls. apply (aTR_keep WW DD _ m mc FP FPT MU);
          [intros x Hx; rewrite HE in Hx; exact Hx | exact FpTLS].
      - exact FpFS.
      - apply fs_frame_shadow_rng; [left; reflexivity|]. unfold rng_shcov, shadow_addr.
        exact (FpFSH FS (FS + FS_SIZE - 1) ltac:(lia) ltac:(unfold FS_SIZE; lia) ltac:(lia)).
      - apply fs_frame_shadow_rng; [right; reflexivity|]. unfold rng_shcov, shadow_addr.
        exact (FpFSH FS (FS + FS_SIZE - 1) ltac:(lia) ltac:(unfold FS_SIZE; lia) ltac:(lia)).
      - eapply rng_sub; [exact (FpO HE) | lia | lia].
      - unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpSoK HE (o + 18) (o + 18 + 32 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact FpROW.
      - unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpSfK f (f + 24 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 2) as [Hk2|Hk2]; [right | left; exact Hk2].
        split; [exact (FpTM Hk2)|].
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpTMK Hk2 (ly_tm row) (ly_tm row + 32 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec g 0) as [G0|G0]; [left; exact G0 | right].
        destruct (Z.eq_dec (ly_al row) 0) as [A0|A0]; [left; exact A0 | right].
        pose proof (rc_u8_range row 17) as R17a. change (rc_u8 row 17) with (ly_al row) in R17a.
        split; [exact (FpG G0 A0)|].
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpGK G0 A0 g (g + ly_al row - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - right; right. split; [exact FpMD|].
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpSmdK md (md + 296 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z_le_dec 3 (ly_k row)) as [L3|L3]; [|left; intros (L3' & _); lia].
        destruct (Z_le_dec (ly_k row) 9) as [L9|L9]; [|left; intros (_ & L9'); lia].
        right; right.
        destruct (Z.eq_dec (ly_bb (ly_k row)) 5) as [B5|B5];
          [|destruct (Z.eq_dec (ly_bb (ly_k row)) 6) as [B6|B6]].
        3: { left. intros [Hb|Hb]; [exact (B5 Hb) | exact (B6 Hb)]. }
        all: right.
        all: destruct (Z.eq_dec (has mb) 0) as [Hh|Hh]; [left; exact Hh | right].
        all: destruct (Z.eq_dec (rname mb) 0) as [Hr|Hr]; [left; exact Hr | right].
        all: assert (NMc : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\
                           has mb <> 0 /\ rname mb <> 0)
               by (split; [split; [lia | first [left; assumption | right; assumption]] | split; assumption]).
        all: pose proof (Hnm NMc) as (Hnok & _); destruct Hnok as (Hnl & _ & _).
        all: split; [exact (FpNB NMc)|];
          unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        all: exact (FpNBK NMc (rname mb) (rname mb + Z.of_nat (length nb) - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 5) as [Hk5|Hk5]; [right | left; exact Hk5].
        split; [exact (FpJ14 Hk5)|].
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpSJ14 Hk5 JOIN_0014 (JOIN_0014 + 32 - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 6) as [Hk6|Hk6]; [right | left; exact Hk6].
        split; [exact (FpJ13 Hk6)|].
        unfold ctrl_lay_block_c.sh_cover, ctrl_lay_block_c.sh_len, ctrl_lay_block_c.sh_lo, shadow_addr.
        exact (FpSJ13 Hk6 JOIN_0013 (JOIN_0013 + 32 - 1) ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
                MU1 & WM1 & MI1 & ST1 & LAY & AC1 & SW1 & AWc1 & FP1 & TL1).
    rewrite Esp in MU1, ST1, AWc1, FP1, TL1.
    unfold CTRL_LAY_BLOCK_K in MU1, ST1, AWc1, FP1, TL1.
    replace (SP0 + -128 - 4512) with LO in MU1, ST1, AWc1, FP1, TL1 by lia.
    fixret.
    (* aJ at the return *)
    assert (MU1' : munch aWlay mc m1).
    { unfold aWlay. unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. exact MU1. }
    assert (AWc1' : addressable m1 (SP0 + -128 - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K)
      by (unfold CTRL_LAY_BLOCK_K; replace (SP0 + -128 - 4512) with LO by lia; exact AWc1).
    assert (FP1' : fp [0%nat; 1%nat] m1 (bv_unsigned tp) FS (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128)
                     (ctrl_lay_block_W o (SP0 + -128)) (ctrl_lay_block_D o f))
      by (unfold CTRL_LAY_BLOCK_K; replace (SP0 + -128 - 4512) with LO by lia; exact FP1).
    pose proof (aJ_lay mc m1 (ctrl_lay_block_W o (SP0 + -128)) (ctrl_lay_block_D o f) HE ltac:(lia)
                  AJ MU1' AC1 SW1 AWc1' FP1') as AJ1.
    (* total munch m -> m1 *)
    assert (MUtot : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m1)
      by (apply (munch_trans _ m mc m1 MU); exact (munch_weaken aWlay _ mc m1 (alay_sub_wlay HE) MU1')).
    assert (WMtot : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc m1 WM WM1)).
    (* f facts at the return *)
    assert (HRf1 : bytes_at rsegs m1 f row)
      by (exact (akeep_bytes f 24 row m1 HR ltac:(rewrite Hrl; reflexivity) AIf ltac:(djl Dsf) ltac:(djl Dof) Hfpwf MUtot)).
    assert (Af1 : addressable m1 f 24)
      by (exact (akeep_addr f 24 m1 Af AIf AIo ltac:(djl Dsf) Hfpwf MUtot)).
    assert (ADf3 : addressable m1 (f + 18) 3)
      by (exact (addressable_sub m1 f 24 18 3 Af1 ltac:(lia) ltac:(lia) ltac:(lia))).
    pose proof MI1 as MIm1.
    (* the frame and the output pieces apart from the block keep their contents across the call *)
    assert (FR1 : rw_cells rsegs m1 (SP0 + -128)
                    (C8 w0 :: C8 (Z_to_bv 64 g) :: C8 (Z_to_bv 64 ns) ::
                     C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
                     C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]))
      by (apply (rw_cells_transport rsegs aWlay mc m1 _ _ FR MU1' WM1); apply alay_dj_fr; [exact HE | reflexivity]).
    assert (P1' : rw_cells rsegs m1 o [CB 6 db])
      by (apply (rw_cells_transport rsegs aWlay mc m1 _ _ P1 MU1' WM1);
          apply alay_dj_out; first [exact HE | exact HDd | (cbn [cells_size csize]; lia)]).
    assert (P2' : rw_cells rsegs m1 (o + 6) [CB 6 sb])
      by (apply (rw_cells_transport rsegs aWlay mc m1 _ _ P2 MU1' WM1);
          apply alay_dj_out; first [exact HE | exact HDd | (cbn [cells_size csize]; lia)]).
    assert (PH12' : bytes_at rsegs m1 (o + 12) HDR).
    { apply (bytes_at_transport rsegs aWlay mc m1 _ _ PH12 MU1').
      assert (LH : Z.of_nat (length HDR) = 6) by reflexivity. rewrite LH.
      apply alay_dj_out; first [exact HE | exact HDd | lia]. }
    assert (HW12' : wr_at rsegs m1 (o + 12) (Z.of_nat 6)) by (exact (wr_at_transport rsegs mc m1 _ _ HW12 WM1)).
    assert (P3' : rw_cells rsegs m1 (o + 12) [CB 6 HDR]) by (exact (em_rw_of rsegs m1 (o + 12) HDR PH12' HW12')).
    assert (P5' : rw_cells rsegs m1 (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply (rw_cells_transport rsegs aWlay mc m1 _ _ P50 MU1' WM1);
          apply alay_dj_out; first [exact HE | exact HDd | (cbn [cells_size csize]; lia)]).
    assert (P6' : rw_cells rsegs m1 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)])
      by (apply (rw_cells_transport rsegs aWlay mc m1 _ _ Pend MU1' WM1);
          apply alay_dj_out; first [exact HE | exact HDd | (cbn [cells_size csize]; lia)]).
    clear FR P1 P2 PH12 HW12 P50 Pend Pblk.
    pose proof AJ1 as AJ1c. destruct AJ1c as (_ & _ & _ & _ & _ & _).
    (* 0x85730 ..: the post-call block, as alay_ret (E3 of the glue draft) *)
    exact (alay_ret (Z_to_bv 64 0x85730) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w0 m1
             HE FR1 ST1 MUtot WMtot MIm1 AJ1 HRf1 Af1 P1' P2' P3' LAY P5' P6').
  Qed.
  (* ==== The entry front (0x853c4 .. 0x8571c): prologue, the EE gate, checked_memset, the two checked_memcpy and
     the header stores (afront_hdr), handed to the continuation at the ctrl_lay_block argument setup. ==== *)

  (* The continuation at the ctrl_lay_block argument setup (0x8571c): the statement of alay_call. *)
  Definition aKont : Prop :=
    forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word) (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    bytes_at rsegs mc (o + 12) HDR -> wr_at rsegs mc (o + 12) (Z.of_nat 6) ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs)).

  (* The state at 0x855a8 (the block length, checked_memset, the row[0]/row[1] loads: aent_ms) as the gate's
     continuation. *)
  Definition aMS : Prop :=
    forall (t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aKont -> EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x855a8) fc None mc (seg_rom rsegs)).

  (* The extra step of a 4-byte check's slow path: addi a6,a6,3 after the andi. *)
  Ltac add3 X := step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia).

  (* The GG gate (0x8553c .. 0x855a8): the checked load of row[22] (GG); when GG = 1, the alignment guard of md,
     the checked 4-byte load of the hid word md + 56, and the early return (s9 = 0, aepi0) when it is 0. *)
  Lemma aent_g2 : forall (t0 t1 t2 x10 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS -> aKont -> (LL = 2 \/ em_wok n = true) ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10
               (zxb (nth 21 row (Z_to_bv 8 0))) (Z_to_bv 64 0) x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x8553c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x10 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK HW FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    pose proof (atr _ mc MU WM (ain_sub LO ltac:(lia))) as (AC1 & SW1 & FP1 & ADT).
    pose proof (ADT _ _ Af) as ADfc. pose proof (ADT _ _ Amd) as ADmc.
    pose proof (em_obj0 rsegs m mc _ _ f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 22 HRc ltac:(lia)) as RD22. change (Z.of_nat 22) with 22 in RD22.
    (* addi a0,s1,22 ; the instrumented check of the byte f + 22 (its slow path writes a6) *)
    step.
    chk_go (f + 22) (Z_to_bv 5 16) (a_shadow mc f 24 (f + 22) 22 ADfc ltac:(lia) ltac:(lia)) (FpSf1 (f + 22) ltac:(lia)) no_extra.
    (* lbu a0,0(a0) ; li a3,1 ; bne a0,a3,85580 *)
    step. step. step.
    pose proof (rc_u8_range row 22) as R22.
    rewrite (rc_u8_eqb row 22 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 22) 1) as [G1|G1]; cbn [negb]; cbv iota.
    - (* GG = 1: andi a0,s6,7 ; bnez a0,85810 : not taken (md mod 8 = 0) *)
      step.
      replace (Z.land (bv_unsigned (Z_to_bv 64 md)) 7) with 0
        by (rewrite unsigned_lit by lia; rewrite rc_land7; symmetry; exact Hmd8).
      step. if_false.
      (* addi a0,s6,56 ; the instrumented check of the 4-byte word md + 56 (its slow path writes a6) *)
      step.
      chk_go (md + 56) (Z_to_bv 5 16)
        (a_shadow4 mc md 296 (md + 56) 56 ADmc ltac:(lia) ltac:(lia) ltac:(rlia) ltac:(lia)) (FpSmd1 (md + 56) ltac:(lia)) add3.
      pose proof (em_obj0 rsegs m mc _ _ md mb 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm) as HMc.
      destruct (rc_rd4_opaque rsegs mc md mb 56 HMc ltac:(lia)) as (L4 & EL4 & RD56).
      change (Z.of_nat 56) with 56 in RD56.
      (* lw a0,0(a0) ; beqz a0,85808 *)
      step. rewrite (em_lw_hid mb L4 EL4).
      step. pose proof (em_hid_range mb) as RH. rewrite em_eqb0 by lia.
      destruct (Z.eqb_spec (em_hid mb) 0) as [H0|H0]; cbv iota.
      + (* 0x85808 : li s9,0 ; j 857c8 ; the early return *)
        step. step.
        assert (HEF : EE = false) by (apply em_E_false_g; assumption).
        eapply evtF_mono;
          [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
      + (* 0x85580 : mv a0,s4 ; beqz a2,855a8 : taken (a2 = 0) *)
        step. step. if_true.
        eapply KMS; [exact HK | apply em_E_true; [exact HW | right; exact H0] | eassumption ..].
    - (* GG <> 1: 0x85580 : mv a0,s4 ; beqz a2,855a8 : taken (a2 = 0) *)
      step. step. if_true.
      eapply KMS; [exact HK | apply em_E_true; [exact HW | left; exact G1] | eassumption ..].
  Qed.

  (* The n check (0x85470 .. 0x85494, LL <> 2): 2 <= n <= 40 and n even, else the early return (s9 = 0, aepi0);
     md <> 0, so the catalogue search (beqz s6 at 0x85488) is not entered. *)
  Lemma aent_nchk : forall (t0 t1 t2 x10 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS -> aKont -> LL <> 2 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x85470) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x10 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK L2 FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    (* addiw a0,s4,-41 ; li a2,-39 ; li s9,0 ; bltu a0,a2,857c8 *)
    do 4 step. rewrite em_wok_ltu by lia.
    destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
    - (* andi a0,s4,1 ; bnez a0,857c8 *)
      step. step. rewrite em_odd by lia.
      destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
      + (* beqz s6,85494 : not taken (md <> 0) ; li a2,0 ; j 8553c *)
        step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
        cbv iota. step. step.
        eapply aent_g2; [exact KMS | exact HK | right | eassumption ..].
        unfold em_wok. rewrite Ev. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia).
        replace (n <=? 40) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + assert (HEF : EE = false)
          by (apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]).
        eapply evtF_mono;
          [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
              by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
              by (symmetry; apply Z.leb_gt; lia); reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
              by (symmetry; apply Z.leb_gt; lia); reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
  Qed.

  (* The LL dispatch (0x8543c .. 0x8553c): the load of row[21] (LL); LL = 2 goes to the gate directly; LL = 0 runs
     the n check (0x8544c) first; LL <> 2 runs the n check at 0x85470 (aent_nchk). *)
  Lemma aent_g1 : forall (t0 t1 t2 x11 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS -> aKont ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 (f + 21))
               x11 x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x8543c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x11 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    pose proof (em_obj0 rsegs m mc _ _ f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 21 HRc ltac:(lia)) as RD21. change (Z.of_nat 21) with 21 in RD21.
    (* lbu a1,0(a0) ; li a0,2 ; beq a1,a0,85488 *)
    step. step. step.
    pose proof (rc_u8_range row 21) as R21.
    rewrite (rc_u8_eqb row 21 2) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbv iota.
    - (* LL = 2: beqz s6,85494 : not taken (md <> 0) ; li a2,0 ; j 8553c *)
      step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
      cbv iota. step. step.
      eapply aent_g2; [exact KMS | exact HK | left; exact L2 | eassumption ..].
    - (* bnez a1,85464 *)
      step. rewrite (rc_u8_eqb row 21 0) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 0) as [L0|L0]; cbn [negb]; cbv iota.
      + (* LL = 0: the n check at 0x8544c (addiw ; li a2,-39 ; li s9,0 ; bltu) *)
        do 4 step. rewrite em_wok_ltu by lia.
        destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
        * step. step. rewrite em_odd by lia.
          destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
          -- (* 0x85464 : bnez s6,85470 : taken (md <> 0) *)
             step. rewrite rc_eqb by lia.
             replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
             eapply aent_nchk; [exact KMS | exact HK | exact L2 | eassumption ..].
          -- assert (HEF : EE = false)
               by (apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]).
             eapply evtF_mono;
               [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
                  by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
                  by (symmetry; apply Z.leb_gt; lia); reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
                  by (symmetry; apply Z.leb_gt; lia); reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0 ms_ HEF HP_) ].
      + (* LL = 1: 0x85464 : bnez s6,85470 : taken (md <> 0) *)
        step. rewrite rc_eqb by lia.
        replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
        eapply aent_nchk; [exact KMS | exact HK | exact L2 | eassumption ..].
  Qed.

  (* The two checked_memcpy calls (0x85628 .. 0x85658: memcpy(o, d, 6) at 0x85638, memcpy(o + 6, s, 6) at 0x8564c,
     each followed by an overflow guard whose branch to unimp at 0x85810 is not taken), then the header stores
     (afront_hdr) and the continuation. The output [o, o + LEN) holds zeros (checked_memset). *)
  Lemma aent_mc : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x21 u3 u4 u5 u6 w0 : word)
      (mc : word -> option byte),
    aKont -> EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc -> wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB (Z.to_nat LEN) (repeat (Z_to_bv 8 0) (Z.to_nat LEN))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               x21 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85628) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x21 u3 u4 u5 u6 w0 mc HK HE FR ST MU WM MI AJ RW0.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (AOo & APo & ART).
    destruct (HEo HE) as (_ & DsoLO & _ & _ & _ & _ & Dod & Dos & _).
    unfold ly_dj in DsoLO.
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (Eo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    (* split the zeroed output: o, o + 6, o + 12 (6 bytes each) and o + 18 (LEN - 18 bytes) *)
    destruct (em_rw_rep rsegs mc o (Z_to_bv 8 0) (Z.to_nat LEN) 6 RW0 ltac:(lia)) as (P1z & R1).
    destruct (em_rw_rep rsegs mc _ (Z_to_bv 8 0) _ 6 R1 ltac:(lia)) as (P2z & R2).
    destruct (em_rw_rep rsegs mc _ (Z_to_bv 8 0) _ 6 R2 ltac:(lia)) as (P3z & P4z).
    replace (o + Z.of_nat 6) with (o + 6) in P2z by lia.
    replace (o + Z.of_nat 6 + Z.of_nat 6) with (o + 12) in P3z by lia.
    replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6) with (o + 18) in P4z by lia.
    replace (Z.to_nat LEN - 6 - 6 - 6)%nat with (Z.to_nat (LEN - 18)) in P4z by lia.
    clear RW0 R1 R2.
    (* local copies of the facts the two checked_memcpy need *)
    pose proof (bytes_at_bound rsegs m d db HD) as BDb. rewrite Hdb in BDb. change (Z.of_nat 6) with 6 in BDb.
    pose proof (bytes_at_bound rsegs m s sb HSb) as BSb. rewrite Hsb in BSb. change (Z.of_nat 6) with 6 in BSb.
    pose proof APD as APDl. pose proof APS as APSl. pose proof HAE as HAEl.
    pose proof Dsd as Dsdl. unfold ly_dj in Dsdl.
    pose proof Dss as Dssl. unfold ly_dj in Dssl.
    pose proof Dod as Dodl. unfold ly_dj in Dodl.
    pose proof Dos as Dosl. unfold ly_dj in Dosl.
    assert (Ed : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by (apply unsigned_lit; lia).
    assert (MKm : meta_kept m mc).
    { apply (munch_meta aWL m mc MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (ADd1 : addressable mc d 6) by (apply (addressable_kept m mc d 6 Ad MKm)).
    assert (ADo1 : addressable mc o 6) by (apply (addressable_prefix mc o LEN 6 AOm); lia).
    assert (HDc1 : bytes_at rsegs mc d db).
    { apply (em_obj rsegs m mc LO SP0 o LEN d db 6 MU HD ltac:(rewrite Hdb; reflexivity));
        [ exact Dsd | exact Dod ]. }
    (* li a2,6 ; li s5,6 ; mv a0,s0 ; mv a1,s7 ; jal checked_memcpy(o, d, 6) *)
    do 5 step.
    pose proof HMC as HMc1.
    unfold asan_memcpy_contract_F, ASAN_MEMCPY_K,
      rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMc1.
    cbv zeta in HMc1.
    (* the footprint premises of asan_memcpy_contract_F for this call, asserted here so that the premise search
       below is pure [exact] (a failing lia inside [first] case-splits on the apartness facts in the context) *)
    assert (FpWc1 : rng RNG (SP0 + -128 - 2224) 2224) by (eapply rng_sub; [exact FpWIN | lia | lia]).
    assert (FpOc1 : rng RNG o 6) by (eapply rng_sub; [exact (FpO HE) | lia | lia]).
    assert (FpIMGc : rng RNG IMG_LO (IMG_HI - IMG_LO))
      by (eapply rng_sub; [exact FpIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia]).
    assert (FpCVw : rng RNG (shadow_addr (SP0 + -128 - 2224) / 8 * 8)
                      (shadow_addr (SP0 + -128 - 2224 + 2224 - 1) / 8 * 8 + 8
                       - shadow_addr (SP0 + -128 - 2224) / 8 * 8))
      by (unfold shadow_addr;
          exact (FpWSH (SP0 + -128 - 2224) (SP0 + -128 - 2224 + 2224 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVo1 : rng RNG (shadow_addr o / 8 * 8)
                       (shadow_addr (o + 6 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8))
      by (unfold shadow_addr; exact (FpSoK HE o (o + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVd1 : rng RNG (shadow_addr d / 8 * 8)
                       (shadow_addr (d + 6 - 1) / 8 * 8 + 8 - shadow_addr d / 8 * 8))
      by (unfold shadow_addr; exact (FpSdK d (d + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    eapply evtF_cut.
    { eapply HMc1 with (src := db) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO); rewrite ?Esp, ?Eo, ?Ed, ?E6;
      first
        [ exact HDc1
        | rewrite Hdb; reflexivity
        | exact P1z
        | exact ADd1
        | exact ADo1
        | exact ST
        | exact HHM
        | exact ACm
        | exact SWm
        | exact MI
        | right; exact (proj1 APDl)
        | right; apply API; lia
        | right; split; [ exact (proj2 APDl) | apply API; lia ]
        | (* footprint: pre-asserted below, so the search runs no lia *)
          exact FpRB | exact FpIMGc | exact FpWc1 | exact FpOc1 | exact FpD
        | right; exact FpCVo1 | right; exact FpCVd1 | right; exact FpCVw
        | lia ]. }
    intros ms2 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SW2).
    rewrite Esp, Eo, E6 in MU2. rewrite Esp in ST2. rewrite Eo, E6 in RW2.
    change (Z.to_nat 6) with 6%nat in RW2, MU2.
    fixret.
    assert (MU2f : munch aWL m m2).
    { apply (munch_trans _ m mc m2 MU).
      apply (munch_weaken [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)]); [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (WM2f : wmono rsegs m m2) by (exact (wmono_trans rsegs m mc m2 WM WM2)).
    assert (SUBw2 : sub_fp [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ2 : aJ m2).
    { apply (aJ_wout [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 API ART AJ MU2 WM2 SUBw2).
      intros x Hx.
      destruct (Z_lt_le_dec x o) as [Lx|Lx]; [left; cbn [outside]; split; [lia | split; [lia | exact I]]|].
      destruct (Z_lt_le_dec x (o + 6)) as [Lx2|Lx2].
      - right. destruct (em_rw_bytes rsegs m2 o 6 db RW2) as (_ & HBo2 & _). destruct HBo2 as (_ & _ & HBf2).
        pose proof (HBf2 (Z.to_nat (x - o)) ltac:(rewrite Hdb; lia)) as HMr2.
        replace (o + Z.of_nat (Z.to_nat (x - o))) with x in HMr2 by lia.
        destruct (nth_error db (Z.to_nat (x - o))) as [bb|] eqn:EN;
          [ exists bb; exact HMr2 | apply nth_error_None in EN; rewrite Hdb in EN; lia ].
      - left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (MKm2 : meta_kept m m2).
    { apply (munch_meta aWL m m2 MU2f). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (FR2 : rw_cells rsegs m2 (SP0 + -128)
                    [CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)); C8 s11; C8 s10; C8 s9; C8 s8;
                     C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ FR MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P2' : rw_cells rsegs m2 (o + 6) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P2z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3' : rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P3z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4' : rw_cells rsegs m2 (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P4z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    (* addi a0,s0,6 ; bgeu s5,a0,85810 : not taken (6 < o + 6, no wrap) *)
    assert (Eo6 : bv_unsigned (Z_to_bv 64 (o + 6)) = o + 6) by (apply unsigned_lit; lia).
    step. step. if_false.
    (* checked_memcpy(o + 6, s, 6) *)
    pose proof AJ2 as AJ2c. destruct AJ2c as (AC2x & SW2x & AW2x & AO2 & FP2x & TL2x).
    assert (Es : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (ADs2 : addressable m2 s 6) by (apply (addressable_kept m m2 s 6 As MKm2)).
    assert (ADo6 : addressable m2 (o + 6) 6) by (apply (addressable_sub m2 o LEN 6 6 AO2); lia).
    assert (HSc2 : bytes_at rsegs m2 s sb).
    { apply (em_obj rsegs m m2 LO SP0 o LEN s sb 6 MU2f HSb ltac:(rewrite Hsb; reflexivity));
        [ exact Dss | exact Dos ]. }
    (* li a2,6 ; mv a1,s8 ; jal checked_memcpy *)
    do 3 step.
    pose proof HMC as HMc2.
    unfold asan_memcpy_contract_F, ASAN_MEMCPY_K,
      rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMc2.
    cbv zeta in HMc2.
    (* the footprint premises of this call (as at the first copy: pure [exact] in the search below) *)
    assert (FpOc2 : rng RNG (o + 6) 6) by (eapply rng_sub; [exact (FpO HE) | lia | lia]).
    assert (FpCVo2 : rng RNG (shadow_addr (o + 6) / 8 * 8)
                       (shadow_addr (o + 6 + 6 - 1) / 8 * 8 + 8 - shadow_addr (o + 6) / 8 * 8))
      by (unfold shadow_addr; exact (FpSoK HE (o + 6) (o + 6 + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVs2 : rng RNG (shadow_addr s / 8 * 8)
                       (shadow_addr (s + 6 - 1) / 8 * 8 + 8 - shadow_addr s / 8 * 8))
      by (unfold shadow_addr; exact (FpSsK s (s + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    eapply evtF_cut.
    { eapply HMc2 with (src := sb) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO); rewrite ?Esp, ?Eo6, ?Es, ?E6;
      first
        [ exact HSc2
        | rewrite Hsb; reflexivity
        | exact P2'
        | exact ADs2
        | exact ADo6
        | exact ST2
        | exact HHM
        | exact AC2
        | exact SW2
        | exact MI2
        | right; exact (proj1 APSl)
        | right; apply API; lia
        | right; split; [ exact (proj2 APSl) | apply API; lia ]
        | (* footprint: pre-asserted below, so the search runs no lia *)
          exact FpRB | exact FpIMGc | exact FpWc1 | exact FpOc2 | exact FpS
        | right; exact FpCVo2 | right; exact FpCVs2 | right; exact FpCVw
        | lia ]. }
    intros ms3 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & RW3 & BD3 & AC3 & SW3).
    rewrite Esp, Eo6, E6 in MU3. rewrite Esp in ST3. rewrite Eo6, E6 in RW3.
    change (Z.to_nat 6) with 6%nat in RW3, MU3.
    fixret.
    assert (MU3f : munch aWL m m3).
    { apply (munch_trans _ m m2 m3 MU2f).
      apply (munch_weaken [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)]); [|exact MU3].
      intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (WM3f : wmono rsegs m m3) by (exact (wmono_trans rsegs m m2 m3 WM2f WM3)).
    assert (SUBw3 : sub_fp [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ3 : aJ m3).
    { apply (aJ_wout [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 API ART AJ2 MU3 WM3 SUBw3).
      intros x Hx.
      destruct (Z_lt_le_dec x (o + 6)) as [Lx|Lx]; [left; cbn [outside]; split; [lia | split; [lia | exact I]]|].
      destruct (Z_lt_le_dec x (o + 6 + 6)) as [Lx2|Lx2].
      - right. destruct (em_rw_bytes rsegs m3 (o + 6) 6 sb RW3) as (_ & HBo3 & _). destruct HBo3 as (_ & _ & HBf3).
        pose proof (HBf3 (Z.to_nat (x - (o + 6))) ltac:(rewrite Hsb; lia)) as HMr3.
        replace (o + 6 + Z.of_nat (Z.to_nat (x - (o + 6)))) with x in HMr3 by lia.
        destruct (nth_error sb (Z.to_nat (x - (o + 6)))) as [bb|] eqn:EN;
          [ exists bb; exact HMr3 | apply nth_error_None in EN; rewrite Hsb in EN; lia ].
      - left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (FR3 : rw_cells rsegs m3 (SP0 + -128)
                    [CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)); C8 s11; C8 s10; C8 s9; C8 s8;
                     C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ FR2 MU3 WM3).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P1'' : rw_cells rsegs m3 o [CB 6 db]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ RW2 MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3'' : rw_cells rsegs m3 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P3' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4'' : rw_cells rsegs m3 (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P4' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    (* E2 of the glue draft: the prefix munch stays tight (aWL), so no widening here. *)
    (* li a0,-13 ; bltu a0,s0,85810 : not taken (o + 1492 <= 2^64) *)
    step. step. if_false.
    (* the header stores (afront_hdr), then the continuation *)
    apply (afront_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns))
             (repeat (Z_to_bv 8 0) 6) HE FR3 ST3 MU3f WM3f MI3 AJ3 P1'' RW3 P3'' P4'').
    intros y10 y11 y12 mc' KMU KWM KMI KAJ KST KFR KP1 KP2 KHB KHW KP18.
    exact (HK _ y10 y11 y12 _ _ _ _ _ _ _ _ _ _ _ _ w0 mc' HE KFR KST KMU KWM KMI KAJ KP1 KP2 KHB KHW KP18).
  Qed.

  (* The block length, the spills of t3, ns and g, checked_memset(o, 0, LEN) at 0x855f8, and the checked loads of
     row[0] (at f) and row[1] (at f + 1) (0x855a8 .. 0x85628). *)
  Lemma aent_ms : forall (t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aKont -> EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x855a8) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j HK HE FR ST MU0 WM MI.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof ST as (Rlo & _ & _).
    destruct (AO HE) as (AOo & APo & ART).
    destruct (HEo HE) as (HOm & DsoLO & Dof & _).
    pose proof DsoLO as DsoLOu. unfold ly_dj in DsoLOu.
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof alay_fs as (_ & _ & _ & FSL).
    pose proof (addressable_app m o LEN AOo) as API.
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app m LO 4640 AWIN) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    (* aJ in the entry memory m (the Section hypotheses, EE = true) *)
    assert (AJm : aJ m).
    { unfold aJ. split; [exact HAC|]. split; [exact HSW|]. split; [exact AWIN|]. split; [exact AOo|].
      split; [pose proof FP as FP'; rewrite HE in FP'; exact FP' | exact FPT]. }
    (* li a2,1 ; sd t3,0(sp) ; sd t4,16(sp) *)
    step. step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc1 end.
    (* the join at 0x855e8 (sd a7,8(sp)): s10 = a5, s8 = s, s9 = LEN; a0 and a1 differ by path *)
    assert (K : forall a0v a1v : word,
      evtF rsegs RNG QK
        (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) a0v a1v
                 (Z_to_bv 64 1) x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g) (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21
                 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5 (Z_to_bv 64 ASAN_K)
                 w0 (Z_to_bv 64 ns) t5 t6)
            F (Z_to_bv 64 0x855e8) fc None mc1 (seg_rom rsegs))).
    { intros a0v a1v.
      (* sd a7,8(sp) *)
      step.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc2 end.
      apply arw_cb3' in FR.
      assert (AJ : aJ mc2) by exact (aJ_win [(LO, SP0)] m mc2 AJm MU0 WM (ain_sub LO ltac:(lia))).
      pose proof AJ as AJc. destruct AJc as (ACm & SWm & _ & AOm & _ & _).
      assert (HOc : rw_cells rsegs mc2 o [CB (Z.to_nat LEN) junk]).
      { apply (rw_cells_transport rsegs [(LO, SP0)] m mc2 o _ HOm MU0 WM).
        cbn [disjoint_from cells_size csize]. lia. }
      assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
      assert (Eo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
      assert (ELEN : bv_unsigned (Z_to_bv 64 LEN) = LEN) by (apply unsigned_lit; lia).
      (* mv a0,s0 ; li a1,0 ; mv a2,s9 ; jal checked_memset *)
      do 4 step.
      pose proof HMS as HMm.
      unfold asan_memset_contract_F, ASAN_MEMSET_K,
        rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMm.
      cbv zeta in HMm.
      (* the footprint premises of asan_memset_contract_F for this call (pure [exact] in the search below) *)
      assert (FpWms : rng RNG (SP0 + -128 - 2208) 2208) by (eapply rng_sub; [exact FpWIN | lia | lia]).
      assert (FpIMGms : rng RNG IMG_LO (IMG_HI - IMG_LO))
        by (eapply rng_sub; [exact FpIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia]).
      assert (FpCVwms : rng RNG (shadow_addr (SP0 + -128 - 2208) / 8 * 8)
                          (shadow_addr (SP0 + -128 - 2208 + 2208 - 1) / 8 * 8 + 8
                           - shadow_addr (SP0 + -128 - 2208) / 8 * 8))
        by (unfold shadow_addr;
            exact (FpWSH (SP0 + -128 - 2208) (SP0 + -128 - 2208 + 2208 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
      assert (FpCVms : rng RNG (shadow_addr o / 8 * 8)
                         (shadow_addr (o + LEN - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8))
        by (unfold shadow_addr; exact (FpSoK HE o (o + LEN - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
      eapply evtF_cut.
      { eapply HMm with (junk := junk) (lo := LO); rewrite ?Esp, ?Eo, ?ELEN;
        first
          [ exact HOc | exact AOm | exact ART | exact ST | exact HHM | exact ACm | exact SWm | exact MI
          | right; exact APo
          | right; apply API; lia
          | destruct DsoLOu as [D1|D1]; solve [ left; lia | right; lia ]
          | (* footprint: pre-asserted below, so the search runs no lia *)
            exact FpRB | exact FpIMGms | exact FpWms | exact (FpO HE)
          | right; exact FpCVms | right; exact FpCVwms
          | lia ]. }
      intros ms' (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m1 & -> & MU1 & WM1
                  & MI1 & ST1 & RW1 & AC1 & SW1).
      rewrite Esp, Eo, ELEN in MU1. rewrite Esp in ST1. rewrite Eo, ELEN in RW1.
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
      fixret.
      assert (SUBw1 : sub_fp [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] aWL).
      { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
      assert (MU : munch aWL m m1).
      { apply (munch_trans _ m mc2 m1).
        - apply em_munch_add; exact MU0.
        - apply (munch_weaken [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)]); [|exact MU1].
          intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
      assert (AJ1 : aJ m1).
      { apply (aJ_wout [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc2 m1 API ART AJ MU1 WM1 SUBw1).
        intros x Hx.
        destruct (Z_lt_le_dec x o) as [Lx|Lx].
        - left. cbn [outside]. split; [lia | split; [lia | exact I]].
        - destruct (Z_lt_le_dec x (o + LEN)) as [Lx2|Lx2].
          + right. destruct (em_rw_bytes rsegs m1 o (Z.to_nat LEN) (repeat (Z_to_bv 8 0) (Z.to_nat LEN)) RW1)
              as (_ & HBo & _).
            destruct HBo as (_ & _ & HBf).
            pose proof (HBf (Z.to_nat (x - o)) ltac:(rewrite repeat_length; lia)) as HMr.
            replace (o + Z.of_nat (Z.to_nat (x - o))) with x in HMr by lia.
            destruct (nth_error (repeat (Z_to_bv 8 0) (Z.to_nat LEN)) (Z.to_nat (x - o))) as [bb|] eqn:EN.
            * exists bb. exact HMr.
            * apply nth_error_None in EN. rewrite repeat_length in EN. lia.
          + left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (FR1 : rw_cells rsegs m1 (SP0 + -128)
                      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
                       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
                       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra])).
      { apply (rw_cells_transport rsegs [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc2 m1 _ _ FR MU1 WM1).
        cbn [disjoint_from cells_size csize Nat.add length]. lia. }
      assert (WMf : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc2 m1 WM WM1)).
      (* the checked loads of row[0] (at f) and row[1] (at f + 1) *)
      assert (MKm : meta_kept m m1).
      { apply (munch_meta aWL m m1 MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
      assert (ADf1 : addressable m1 f 24) by (apply (addressable_kept m m1 f 24 Af MKm)).
      assert (HRm1 : bytes_at rsegs m1 f row).
      { apply (em_obj rsegs m m1 LO SP0 o LEN f row 24 MU HR ltac:(rewrite Hrl; reflexivity));
          [ exact Dsf | exact Dof ]. }
      pose proof (rd_byte rsegs m1 f row 0 HRm1 ltac:(lia)) as RD0.
      replace (f + Z.of_nat 0) with f in RD0 by lia.
      pose proof (rd_byte rsegs m1 f row 1 HRm1 ltac:(lia)) as RD1.
      change (Z.of_nat 1) with 1 in RD1.
      (* srli a0,s1,3 ; add a0,a0,s11 ; lb a0,0(a0) ; bnez a0,8582c: the slow path 0x8582c is blt s2,a0,8560c
         with s2 = 0, taken because f mod 8 = 0 < k; either way the state at 0x8560c is the same *)
      destruct (a_shadow m1 f 24 f 0 ADf1 ltac:(lia) ltac:(lia)) as (k & RK & OK & KR).
      pose proof (FpSf1 f ltac:(lia)) as RSf0.
      step. rewrite ?(unsigned_lit f) by lia. rewrite rc_shr3.
      step. step. clear RK RSf0. steps_until_if.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      lazymatch goal with
      | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : evtF segs RNG0 Q (MS R F B fc rv mm ro));
          [ destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ exact G
            | cbv iota; step;
              rewrite (rc_lts_signed 0 (bv_signed k)) by lia;
              replace (0 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; rewrite Hf8 in OK; destruct OK; lia);
              cbv iota; exact G ]
          | ]
      end.
      clear OK KR.
      (* addi a0,s1,1 ; the check of f + 1 (srli a1 ; add a1 ; lb a1 ; lbu s3,0(s1) = row[0] ; bnez a1,85838;
         slow path 0x85838: andi a2,a0,7 ; blt a2,a1,85624) *)
      step.
      chk_go (f + 1) (Z_to_bv 5 12) (a_shadow m1 f 24 (f + 1) 1 ADf1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 1) ltac:(lia)) no_extra.
      (* lbu s2,0(a0) = row[1] *)
      step.
      eapply aent_mc;
        [ exact HK | exact HE | exact FR1 | exact ST1 | exact MU | exact WMf | exact MI1 | exact AJ1 | exact RW1 ].
    }
    (* beq a1,a2,855d4 (a1 = LL, a2 = 1) *)
    step.
    pose proof (rc_u8_range row 21) as R21.
    rewrite (rc_u8_eqb row 21 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 1) as [L1|L1]; cbv iota.
    - (* LL = 1, 0x855d4: mv s10,a5 ; mv s8,a4 ; li a1,36 ; mul a0,a0,a1 ; addi s9,a0,52 *)
      assert (L2n : LL <> 2) by (unfold ubat; unfold rc_u8 in L1; lia).
      pose proof (em_E_wok _ _ _ _ HE L2n) as W.
      do 5 step. rewrite (em_len_word n W).
      replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
        by (unfold em_len; rewrite (proj2 (Z.eqb_neq (ubat row 21) 2) L2n); reflexivity).
      apply K.
    - (* li a0,2 ; bne a1,a0,855d0 *)
      step. step. rewrite (rc_u8_eqb row 21 2) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbn [negb]; cbv iota.
      + (* LL = 2: mv s10,a5 ; mv s8,a4 ; li s9,1492 ; j 855e8 *)
        do 4 step.
        replace (Z_to_bv 64 1492) with (Z_to_bv 64 LEN)
          by (unfold em_len; rewrite (proj2 (Z.eqb_eq (ubat row 21) 2) L2); reflexivity).
        apply K.
      + (* LL = 0, 0x855d0: mv a0,s4 ; then as LL = 1 *)
        assert (L2n : LL <> 2) by exact L2.
        pose proof (em_E_wok _ _ _ _ HE L2n) as W.
        do 6 step. rewrite (em_len_word n W).
        replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
          by (unfold em_len; rewrite (proj2 (Z.eqb_neq (ubat row 21) 2) L2n); reflexivity).
        apply K.
  Qed.

  (* The entry front (0x853c4 ..): the prologue (the 13 register saves into the frame at SP0 + -128), the checks
     f <> 0 and f mod 8 = 0 (branches to unimp at 0x85810 not taken), the load of the shadow base ASAN_K into s11,
     and the checked byte f + 21, then aent_g1. The hypothesis is the statement of alay_call. *)
  Lemma aentry_k :
    (forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word) (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    bytes_at rsegs mc (o + 12) HDR -> wr_at rsegs mc (o + 12) (Z.of_nat 6) ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs))) ->
    forall (t0 t1 t2 t3 t5 t6 : word),
    evtF rsegs RNG QK
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x853c4) fc None m (seg_rom rsegs)).
  Proof.
    intros HK t0 t1 t2 t3 t5 t6.
    (* the prologue's stores write m itself: keep closed copies of the Section facts used after them *)
    pose proof aent_g1 as G1. pose proof aent_ms as KMS0. pose proof atr as ATR. pose proof a_shadow as ASH.
    pose proof (ain_sub (bv_unsigned sp - 4640) ltac:(lia)) as AIN.
    pose proof arng_sp as Rsp.
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp - 4640, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp - 4640, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. unfold HIGHMEM_BEG in HHM.
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    (* addi sp,sp,-128 ; the 13 saves *)
    step. carve_frame 128%nat ST. do 13 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    (* beqz a1,85810 : not taken (f <> 0) *)
    step. rewrite rc_eqb by lia. replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf0). cbv iota.
    (* mv s1,a1 ; andi s2,a1,7 ; bnez s2,85810 : not taken (f mod 8 = 0) *)
    step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 f)) 7) with 0
      by (rewrite unsigned_lit by lia; rewrite rc_land7; symmetry; exact Hf8).
    step. if_false.
    (* mv s4,a6 ; mv s7,a3 ; mv s6,a2 ; mv s0,a0 ; auipc ; ld (GOT) ; ld s11 (ASAN_K) *)
    do 7 step.
    clear RG RC.
    (* addi a0,s1,21 ; the instrumented check of the byte f + 21 *)
    step.
    pose proof (ATR _ m1 MU WM AIN) as (AC1 & SW1 & FP1 & ADT1).
    pose proof (ADT1 _ _ Af) as ADf1.
    chk_go (f + 21) (Z_to_bv 5 12) (ASH m1 f 24 (f + 21) 21 ADf1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 21) ltac:(lia)) no_extra.
    eapply G1; [exact KMS0 | exact HK | eassumption ..].
  Qed.


  (* ========================================================================================================== *)
  (* Route (C) _on forms (a Theorem Labs lane 2026-10-29 09:20Z; a Theorem Labs lane, for a Theorem Labs lane's glue
     C_ctrl_emit_as.v): the two stretch lemmas the glue cites -- aentry_k (stretch 1: the entry .. the ctrl_lay_block
     argument setup) and alay_ret (stretch 3: ctrl_lay_block's return .. the end) -- and what they use, with the
     UNIVERSAL shadow_rw replaced.  Every name and text above is unchanged; each X_on below is X's text with:
     - HSW : shadow_rw m  ->  HSW_on : shadow_rw_on ctrl_emit_as_stretch_shadow_R m (used only at the three runtime-helper
       calls of stretch 1; stretch 3 needs no shadow premise);
     - aJ's conjunct shadow_rw mc  ->  aJ_on's transport `forall P, shadow_rw_on P m -> shadow_rw_on P mc` (every
       shadow region present at the stretch base m is present at mc), and aQp's post conjunct shadow_rw m' -> the
       same transport to m' (the route (C) post form);
     - the callee hypotheses HMS / HMC / HFN  ->  the callees' _on contracts asan_memset_contract_F_on and
       asan_memcpy_contract_F_on (a Theorem Labs lane's texts, lib/B/Prog/asan_memset_cF_on.v, asan_memcpy_cF_on.v) and
       ctrl_finish_contract_F_on (premise-free, a Theorem Labs lane's lib/B/Prog/ctrl_finish_c.v); HBR (reac_braid_encode_ns0)
       has no shadow premise and stays.
     ctrl_emit_as_stretch_shadow_R is MEASURED from the two stretches.  They STORE no shadow byte: their munch rows are the
     window [LO, SP0), the output [o, o + LEN) and the callees' frames (asan_memset / asan_memcpy: the destination
     and the helper's stack; ctrl_finish: its frame and fin_w; reac_braid_encode: its frame).  They READ the shadow
     of: the instrumented checks of the row bytes f, f + 1, f + 21, f + 22, f + 23, of md + 56 (4 bytes), of the
     output bytes o + 12 .. o + 17 and o + LEN - 2, o + LEN - 1; checked_memset's region sh_word_on o LEN; the two
     checked_memcpy regions sh_word_on d 6 \/ sh_word_on o 6 and sh_word_on s 6 \/ sh_word_on (o + 6) 6; ctrl_finish's
     checks of f + 18 .. f + 20 and o + 18 .. o + 49.  As 8-aligned word covers: f's 24 row bytes, md's 296 model
     bytes, d's and s's 6 bytes and, when EE = true, the LEN output bytes.  The window's shadow is NOT read: the
     footprint row FpWSH is there because the helpers' _F contracts ask for the shadow span of their own frame, and
     asan_memset_c_on.v / asan_memcpy_c_on.v record that the helper's frame shadow is not read through shadow_rw.
     The side-stack shadow (fp_w) and the window's shadow are written only by ctrl_lay_block (stretch 2, the
     glue's cut). *)
  Definition ctrl_emit_as_stretch_shadow_R (a : Z) : Prop :=
    sh_word_on f 24 a \/ sh_word_on md 296 a \/ sh_word_on d 6 a \/ sh_word_on s 6 a \/
    (EE = true /\ sh_word_on o LEN a).

  Hypothesis HSW_on : shadow_rw_on ctrl_emit_as_stretch_shadow_R m.
  Hypothesis HMS_on : asan_memset_contract_F_on.
  Hypothesis HMC_on : asan_memcpy_contract_F_on.
  Hypothesis HFN_on : ctrl_finish_contract_F_on.

  (* aJ with the shadow conjunct as the route (C) transport from the stretch base m. *)
  Definition aJ_on (mc : word -> option byte) : Prop :=
    asan_cells mc /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc) /\
    addressable mc LO 4640 /\ addressable mc o LEN /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 aWL aDL /\ aTL mc.

  (* aQp with the route (C) post: the transport from m to m'. *)
  Definition aQp_on : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (EE = true -> aRES m').

  Hypothesis HQK0_on : forall ms, EE = false -> aQp_on ms -> QK ms.

  (* The transport survives writes apart from the shadow (ae_fl_shadow_rw_on). *)
  Lemma ae_tr_munch : forall W' m1 m2, (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m1) ->
    munch W' m1 m2 -> wmono rsegs m1 m2 -> (forall x, in_shadow x -> outside W' x) ->
    forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m2.
  Proof. intros W' m1 m2 TR MU WM SHo P HP. exact (ae_fl_shadow_rw_on P W' m1 m2 (TR P HP) MU WM SHo). Qed.

  (* checked_memset(o, 0, LEN)'s region (asan_memset_shadow_R) from the transport and HSW_on. *)
  Lemma ae_srw_ms : forall mc A0 A2, bv_unsigned A0 = o -> bv_unsigned A2 = LEN -> EE = true ->
    (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc) -> shadow_rw_on (asan_memset_shadow_R A0 A2) mc.
  Proof.
    intros mc A0 A2 E0 E2 HE TR.
    apply (shadow_rw_on_mono ctrl_emit_as_stretch_shadow_R); [|exact (TR _ HSW_on)].
    intros a Ha. unfold asan_memset_shadow_R in Ha. rewrite E0, E2 in Ha.
    unfold ctrl_emit_as_stretch_shadow_R. right; right; right; right. split; [exact HE | exact Ha].
  Qed.

  (* checked_memcpy(D0, S0, 6)'s region (asan_memcpy_shadow_R) for D0 inside the output and S0 = d or s. *)
  Lemma ae_srw_mc : forall mc A0 A1 A2 D0 S0, bv_unsigned A0 = D0 -> bv_unsigned A1 = S0 -> bv_unsigned A2 = 6 ->
    EE = true -> o <= D0 -> D0 + 6 <= o + LEN -> (S0 = d \/ S0 = s) ->
    (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc) -> shadow_rw_on (asan_memcpy_shadow_R A0 A1 A2) mc.
  Proof.
    intros mc A0 A1 A2 D0 S0 E0 E1 E2 HE H1 H2 HS TR.
    apply (shadow_rw_on_mono ctrl_emit_as_stretch_shadow_R); [|exact (TR _ HSW_on)].
    intros a Ha. unfold asan_memcpy_shadow_R in Ha. rewrite E0, E1, E2 in Ha.
    unfold ctrl_emit_as_stretch_shadow_R. destruct Ha as [Ha|Ha].
    - destruct HS as [-> | ->]; [right; right; left; exact Ha | right; right; right; left; exact Ha].
    - right; right; right; right. split; [exact HE|].
      exact (ae_sh_word_on_sub o LEN D0 6 a H1 H2 ltac:(lia) Ha).
  Qed.

  (* aJ_win with aJ_on. *)
  Lemma aJ_win_on : forall W' m1 m2, aJ_on m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(LO, SP0)] -> aJ_on m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & AWo & FPc & TL) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (ae_tr_munch W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W' FPc MU WM Hs).
    - exact (fl_tls _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* aJ_out with aJ_on. *)
  Lemma aJ_out_on : forall W' m1 m2, app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) ->
    aJ_on m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(o, o + LEN)] ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> aJ_on m2.
  Proof.
    intros W' m1 m2 Hap HRT (AC & SW & AW & AWo & FPc & TL) MU WM Hs RD.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; apply Hs; cbn [outside]; split; [pose proof (app_ivl_meta o (o + LEN) x Hap Hx); lia | exact I]).
    assert (SWW : sub_fp W' aWL)
      by (intros x Hx; apply Hs; cbn [outside] in Hx |- *; destruct Hx as (_ & H2 & _); split; [exact H2 | exact I]).
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply Hs. cbn [outside].
      split; [unfold RT_LO, RT_HI in *; lia | exact I].
    - exact (ae_tr_munch W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM SWW RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU SWW TL).
  Qed.

  (* aJ_wout with aJ_on. *)
  Lemma aJ_wout_on : forall W' m1 m2, app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) ->
    aJ_on m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' aWL ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> aJ_on m2.
  Proof.
    intros W' m1 m2 Hap HRT (AC & SW & AW & AWo & FPc & TL) MU WM Hs RD.
    assert (SHo : forall x, in_shadow x -> outside W' x).
    { intros x Hx. apply Hs. cbn [outside].
      pose proof (app_ivl_meta o (o + LEN) x Hap Hx) as Ho2.
      split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx, HHM; lia
             | split; [lia | exact I]]. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply Hs. cbn [outside].
      split; [unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia
             | split; [unfold RT_LO, RT_HI in *; lia | exact I]].
    - exact (ae_tr_munch W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM Hs RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* aJ_ostore with aJ_on. *)
  Lemma aJ_ostore_on : forall mc (a : Z) (b : byte),
    aJ_on mc -> app_ivl o (o + LEN) -> (o + LEN <= RT_LO \/ RT_HI <= o) -> o <= a < o + LEN ->
    aJ_on (write_to_mem mc (wa a) [b]).
  Proof.
    intros mc a b AJ API ART Ha.
    pose proof AJ as AJ2. destruct AJ2 as (_ & _ & _ & AOw & FPc & _).
    pose proof AOw as (Ho0 & _ & HoE & _). unfold APPMEM_END in HoE.
    pose proof FPc as FP2. destruct FP2 as (DT & TS & C & T & DB & k & _ & _ & HP & _).
    destruct HP as (_ & _ & _ & _ & P5).
    apply (aJ_out_on [(a, a + 1)] mc (write_to_mem mc (wa a) [b]) API ART AJ).
    - apply munch_write; cbn [length inside]; [apply munch_refl | lia | lia | left; split; lia].
    - apply wmono_write, wmono_refl.
    - intros x Hx. cbn [outside] in *. destruct Hx as (H1 & _). split; [lia | exact I].
    - intros x Hx. right.
      pose proof (stk_write rsegs mc FS (FS + FS_SIZE) a [b] P5 ltac:(lia) ltac:(cbn [length]; lia)) as STw.
      destruct STw as (_ & _ & STwf). destruct (STwf x Hx) as (_ & HB). exact HB.
  Qed.

  (* aJ_lay with aJ_on: at ctrl_lay_block's return the callee's _on post gives the transport from its entry memory mc
     (ctrl_lay_block_contract_F_on, a Theorem Labs lane's lib/B/Prog/ctrl_lay_block_c.v _on block); composed with aJ_on mc's transport
     from m.  For the whole-function _on theorem (a Theorem Labs lane); stretches 1 and 3 do not use it. *)
  Lemma aJ_lay_on : forall (mc m1 : word -> option byte) (W' D' : list ivl),
    EE = true -> 52 <= LEN ->
    aJ_on mc -> munch aWlay mc m1 ->
    asan_cells m1 -> (forall P : Z -> Prop, shadow_rw_on P mc -> shadow_rw_on P m1) ->
    addressable m1 (SP0 + -128 - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    fp [0%nat; 1%nat] m1 (bv_unsigned tp) FS (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) W' D' ->
    aJ_on m1.
  Proof.
    intros mc m1 W' D' HE HLe AJ MU AC1 SW1 AWc1 FP1.
    destruct AJ as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    pose proof arng_sp as RSP.
    pose proof (addressable_app mc o LEN AOm) as AIo.
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as AIw0.
      apply (app_ivl_sub LO (LO + 4640) LO SP0 AIw0); lia. }
    assert (HIno : In (o, o + LEN) aDL) by (cbn [In]; right; right; right; right; left; reflexivity).
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    pose proof FPm as FPd.
    destruct FPd as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    assert (SUB : sub_fp aWlay (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)])).
    { intros x Hx. cbn [outside app] in Hx. destruct Hx as (Hlo & Ho_ & Hrest).
      destruct (alay_oai (fp_w [0%nat; 1%nat] FS) [(shadow_addr LO, shadow_addr SP0)] x Hrest) as (Hfpw_x & HY_x).
      cbn [outside] in HY_x. destruct HY_x as (HYx & _).
      apply fl_out_app; [| apply fl_out_app].
      - cbn [outside]. split; [|split; [|exact I]].
        + intros [A1 A2]. apply Ho_; lia.
        + intros [A1 A2]. apply Hlo; unfold CTRL_LAY_BLOCK_K in *; lia.
      - exact Hfpw_x.
      - cbn [outside]. split; [|exact I]. intros [A1 A2]. apply HYx. split.
        + replace (shadow_addr LO) with (shadow_addr (SP0 + -128 - CTRL_LAY_BLOCK_K));
            [exact A1 | f_equal; unfold CTRL_LAY_BLOCK_K; lia].
        + pose proof (alay_shge SP0 (SP0 + -128) ltac:(lia)) as G. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - exact AC1.
    - exact (fun (P : Z -> Prop) (HP : shadow_rw_on P m) => SW1 P (SWm P HP)).
    - assert (AWlo : addressable m1 LO CTRL_LAY_BLOCK_K).
      { replace LO with (SP0 + -128 - CTRL_LAY_BLOCK_K) by (unfold CTRL_LAY_BLOCK_K; lia). exact AWc1. }
      assert (AWfr : addressable m1 (LO + CTRL_LAY_BLOCK_K) 128).
      { apply (alay_akeep aWlay mc m1 (LO + CTRL_LAY_BLOCK_K) 128).
        - apply (addressable_sub mc LO 4640 CTRL_LAY_BLOCK_K 128 AWm); unfold CTRL_LAY_BLOCK_K; lia.
        - exact MU.
        - intros i Hi. apply (alay_sh (LO + CTRL_LAY_BLOCK_K + i)).
          + apply AIwS; unfold CTRL_LAY_BLOCK_K in *; lia.
          + exact AIo.
          + exact AIwS.
          + exact Fmod.
          + exact Fapp.
          + apply alay_outfpw_hi.
            * apply AIwS; unfold CTRL_LAY_BLOCK_K in *; lia.
            * exact FSpos.
            * exact Fmod.
            * unfold CTRL_LAY_BLOCK_K in *; lia.
            * unfold CTRL_LAY_BLOCK_K in *; lia.
          + right; unfold CTRL_LAY_BLOCK_K in *; lia.
          + exact HLe. }
      exact (alay_ajoin m1 LO CTRL_LAY_BLOCK_K 128 AWlo AWfr ltac:(lia)).
    - apply (alay_akeep aWlay mc m1 o LEN AOm MU).
      intros i Hi. apply (alay_sh (o + i)).
      + apply AIo; lia.
      + exact AIo.
      + exact AIwS.
      + exact Fmod.
      + exact Fapp.
      + exact (fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) o (o + LEN) (o + i) HDd HIno ltac:(lia)).
      + destruct DsoLO as [Hdj|Hdj]; [right; lia | left; unfold CTRL_LAY_BLOCK_K in *; lia].
      + exact HLe.
    - exact (fl_fp_ret [0%nat; 1%nat] mc m1 (bv_unsigned tp) FS LO SP0 aWL aDL
               [(shadow_addr LO, shadow_addr SP0)] aWlay
               (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128) W' D' FPm TLm MU SUB FP1).
    - unfold aTL, ctrl_emit_as_tls. intros DT TS C T DB k HT1.
      destruct FPm as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
      assert (Htc : Forall (fun d => forall y, fst d <= y < snd d -> outside aWlay y)
                     (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
      { apply Forall_forall. intros [a b] Hin y Hy. apply SUB. apply fl_out_app.
        - exact (fl_dj_out aWL _ a b y HWd (in_or_app _ _ _ (or_introl Hin)) Hy).
        - exact (fl_dj_out_r _ _ a b y (TLm _ _ _ _ _ _ HT0) Hin Hy). }
      destruct (fl_tls_same mc m1 aWlay (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT1 MU Htc)
        as (E1 & E2 & E3 & E4 & E5 & E6).
      subst. exact (TLm DT TS C T DB k HT0).
  Qed.

  (* atr with the transport from m. *)
  Lemma atr_on : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc) /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p q, addressable m p q -> addressable mc p q).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split]].
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fun (P : Z -> Prop) (HP : shadow_rw_on P m) => ae_fl_shadow_rw_on P W' m mc HP MU WM SHo).
    - exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
    - intros p q H. exact (fl_addressable W' m mc p q H MU SHo).
  Qed.

  (* aepi with the transport and aQp_on. *)
  Lemma aepi_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte) (r : Z),
    r = RR -> 0 <= r < 2^64 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc ->
    asan_cells mc -> (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc) ->
    addressable mc LO 4640 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD ->
    (EE = true -> aRES mc) ->
    evtF rsegs RNG aQp_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 (Z_to_bv 64 r) x26 x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x857c8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 u3 u4 u5 u6
      mc j r Er Rr FR ST MU WM MI AC SW AW FP' HRES.
    pose proof arng_sp as Rsp.
    pose proof ST as (Rlo & _ & _).
    do 16 step.
    apply evtF_done. unfold aQp_on.
    do 14 eexists. exists mc. rewrite Er.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP'|].
    exact HRES.
  Qed.

  (* aepi0 with atr_on / aepi_on. *)
  Lemma aepi0_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    EE = false ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aQp_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 (Z_to_bv 64 0) x26 x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x857c8) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 u3 u4 u5 u6
      mc j HE FR ST MU WM MI.
    pose proof arng_sp as Rsp.
    destruct (atr_on _ mc MU WM (ain_sub LO ltac:(lia))) as (AC & SW & FP' & ADT).
    apply (aepi_on x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
             u3 u4 u5 u6 mc j 0);
      [rewrite HE; reflexivity | lia | exact FR | exact ST | | exact WM | exact MI
       | exact AC | exact SW | exact (ADT _ _ AWIN) | exact FP' | rewrite HE; intros H; discriminate H].
    apply (munch_weaken [(LO, SP0)]); [|exact MU].
    intros x Hx. rewrite HE in Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I].
  Qed.

  (* afront_hdr with aJ_on. *)
  Lemma afront_hdr_on : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
      (mc : word -> option byte) (jf jh : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 jh] ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    (forall (y10 y11 y12 : word) (mc' : word -> option byte),
       munch aWL m mc' ->
       wmono rsegs m mc' -> mem_inv rsegs mc' -> aJ_on mc' ->
       stk rsegs mc' LO (SP0 + -128) ->
       rw_cells rsegs mc' (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                        C8 s2; C8 s1; C8 s0; C8 ra] ->
       rw_cells rsegs mc' o [CB 6 db] -> rw_cells rsegs mc' (o + 6) [CB 6 sb] ->
       bytes_at rsegs mc' (o + 12) HDR -> wr_at rsegs mc' (o + 12) (Z.of_nat 6) ->
       rw_cells rsegs mc' (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
       evtF rsegs RNG QK
         (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
                  x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
                  (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
                  (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
             F (Z_to_bv 64 0x8571c) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85658) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc jf jh
      HE FR ST MU WM MI AJ P1 P2 P12 P18 Hcont.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (FpO HE) as FpOc.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    pose proof (unsigned_lit o ltac:(lia)) as Hou.
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_bytes rsegs mc (o + 12) 6 jh P12) as (HL12 & _ & HW12). clear P12.
    (* ===== store 1: o + 12 := 136 ===== *)
    step.
    destruct (a_out0 mc 12 AOm ltac:(lia) ltac:(lia)) as (k1 & RK1 & K01).
    chk0 (o + 12) k1 RK1 K01 (FpSo1 HE (o + 12) ltac:(lia)).
    assert (HSa : store_ok rsegs mc (wa (o + 12)) 1 = true).
    { pose proof (wr_at_store_ok rsegs mc (o + 12) (Z.of_nat 6) 0 1%nat HW12 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    step. step. step.
    replace (o + 12 + Z.of_nat 0) with (o + 12) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 136) by lia.
    step. if_false.
    assert (MU1 : munch aWL m (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM1 : wmono rsegs m (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136])) by (apply wmono_write; exact WM).
    assert (MI1 : mem_inv rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply mem_inv_store; [exact MI | cbn [length]; exact HSa]).
    assert (AJ1 : aJ_on (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]))
      by (apply (aJ_ostore_on mc (o + 12) (Z_to_bv 8 136)); [exact AJ | exact API | exact ART | lia]).
    assert (FR1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST1 : stk rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) LO (SP0 + -128))
      by (apply stk_write; [exact ST | lia | cbn [length]; lia]).
    assert (P1_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_1 : rw_cells rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HB1 : bytes_at rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 12) [Z_to_bv 8 136])
      by (apply bytes_at_write_same; cbn [length]; lia).
    assert (HW1 : wr_at rsegs (write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW12).
    try fold (wa (o + 12)).
    set (m1 := write_to_mem mc (wa (o + 12)) [Z_to_bv 8 136]) in *. clearbody m1.
    pose proof AJ1 as AJ1c. destruct AJ1c as (_ & _ & _ & AO1 & _ & _).
    (* ===== store 2: o + 13 := 25 ===== *)
    step.
    destruct (a_out0 m1 13 AO1 ltac:(lia) ltac:(lia)) as (k2 & RK2 & K02).
    chk0 (o + 13) k2 RK2 K02 (FpSo1 HE (o + 13) ltac:(lia)).
    assert (HSok2 : store_ok rsegs m1 (wa (o + 13)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m1 (o + 12) (Z.of_nat 6) 1 1%nat HW1 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 1) with (o + 13) in H by lia. exact H. }
    step. step. step.
    replace (o + 13 + Z.of_nat 0) with (o + 13) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 25) by lia.
    step. if_false.
    assert (MU2 : munch aWL m (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply munch_write; [exact MU1 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM2 : wmono rsegs m (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25])) by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply mem_inv_store; [exact MI1 | cbn [length]; exact HSok2]).
    assert (AJ2 : aJ_on (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]))
      by (apply (aJ_ostore_on m1 (o + 13) (Z_to_bv 8 25)); [exact AJ1 | exact API | exact ART | lia]).
    assert (FR2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR1 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST2 : stk rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) LO (SP0 + -128))
      by (apply stk_write; [exact ST1 | lia | cbn [length]; lia]).
    assert (P1_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_2 : rw_cells rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_1 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW2 : wr_at rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW1).
    assert (HBy2 : bytes_at rsegs (write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) (o + 12)
                     [Z_to_bv 8 136; Z_to_bv 8 25]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25] with ([Z_to_bv 8 136] ++ [Z_to_bv 8 25]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 1) with (o + 13) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 13)).
    set (m2 := write_to_mem m1 (wa (o + 13)) [Z_to_bv 8 25]) in *. clearbody m2.
    pose proof AJ2 as AJ2c. destruct AJ2c as (_ & _ & _ & AO2 & _ & _).
    (* ===== store 3: o + 14 := low byte of a5 ===== *)
    step.
    destruct (a_out0 m2 14 AO2 ltac:(lia) ltac:(lia)) as (k3 & RK3 & K03).
    chk0 (o + 14) k3 RK3 K03 (FpSo1 HE (o + 14) ltac:(lia)).
    assert (HSc : store_ok rsegs m2 (wa (o + 14)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m2 (o + 12) (Z.of_nat 6) 2 1%nat HW2 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 2) with (o + 14) in H by lia. exact H. }
    step. step.
    replace (o + 14 + Z.of_nat 0) with (o + 14) by lia.
    rewrite ?em_le1. rewrite (em_c16_lo a5).
    step. if_false.
    assert (MU3 : munch aWL m (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply munch_write; [exact MU2 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM3 : wmono rsegs m (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply wmono_write; exact WM2).
    assert (MI3 : mem_inv rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply mem_inv_store; [exact MI2 | cbn [length]; exact HSc]).
    assert (AJ3 : aJ_on (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]))
      by (apply (aJ_ostore_on m2 (o + 14) (Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)));
          [exact AJ2 | exact API | exact ART | lia]).
    assert (FR3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR2 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST3 : stk rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    LO (SP0 + -128)) by (apply stk_write; [exact ST2 | lia | cbn [length]; lia]).
    assert (P1_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    o [CB 6 db]) by (apply rw_cells_frame; [exact P1_2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (o + 6) [CB 6 sb]) by (apply rw_cells_frame; [exact P2_2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_3 : rw_cells rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                      (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_2 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW3 : wr_at rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                    (o + 12) (Z.of_nat 6)) by (apply wr_at_write; exact HW2).
    assert (HBy3 : bytes_at rsegs (write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)])
                     (o + 12) [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25] ++ [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy2 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 2) with (o + 14) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 14)).
    set (m3 := write_to_mem m2 (wa (o + 14)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]) in *. clearbody m3.
    pose proof AJ3 as AJ3c. destruct AJ3c as (_ & _ & _ & AO3 & _ & _).
    (* ===== store 4: o + 15 := high byte of a5 ===== *)
    step.
    destruct (a_out0 m3 15 AO3 ltac:(lia) ltac:(lia)) as (k4 & RK4 & K04).
    chk0 (o + 15) k4 RK4 K04 (FpSo1 HE (o + 15) ltac:(lia)).
    assert (HSd : store_ok rsegs m3 (wa (o + 15)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m3 (o + 12) (Z.of_nat 6) 3 1%nat HW3 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 3) with (o + 15) in H by lia. exact H. }
    step. step. step.
    replace (o + 15 + Z.of_nat 0) with (o + 15) by lia.
    rewrite ?em_le1. rewrite (em_c16_hi a5).
    step. if_false.
    assert (MU4 : munch aWL m (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply munch_write; [exact MU3 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM4 : wmono rsegs m (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply wmono_write; exact WM3).
    assert (MI4 : mem_inv rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply mem_inv_store; [exact MI3 | cbn [length]; exact HSd]).
    assert (AJ4 : aJ_on (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]))
      by (apply (aJ_ostore_on m3 (o + 15) (Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)));
          [exact AJ3 | exact API | exact ART | lia]).
    assert (FR4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR3 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST4 : stk rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    LO (SP0 + -128)) by (apply stk_write; [exact ST3 | lia | cbn [length]; lia]).
    assert (P1_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    o [CB 6 db]) by (apply rw_cells_frame; [exact P1_3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (o + 6) [CB 6 sb]) by (apply rw_cells_frame; [exact P2_3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_4 : rw_cells rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                      (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_3 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW4 : wr_at rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                    (o + 12) (Z.of_nat 6)) by (apply wr_at_write; exact HW3).
    assert (HBy4 : bytes_at rsegs (write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)])
                     (o + 12) [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
                               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
              Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256)]
              ++ [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy3 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 3) with (o + 15) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 15)).
    set (m4 := write_to_mem m3 (wa (o + 15)) [Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)]) in *. clearbody m4.
    pose proof AJ4 as AJ4c. destruct AJ4c as (_ & _ & _ & AO4 & _ & _).
    (* ===== store 5: o + 16 := row[0] ===== *)
    step.
    destruct (a_out0 m4 16 AO4 ltac:(lia) ltac:(lia)) as (k5 & RK5 & K05).
    chk0 (o + 16) k5 RK5 K05 (FpSo1 HE (o + 16) ltac:(lia)).
    assert (HSe : store_ok rsegs m4 (wa (o + 16)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m4 (o + 12) (Z.of_nat 6) 4 1%nat HW4 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 4) with (o + 16) in H by lia. exact H. }
    step. step.
    replace (o + 16 + Z.of_nat 0) with (o + 16) by lia.
    rewrite ?em_le1. rewrite (em_byte_zxb (nth 0 row (Z_to_bv 8 0))).
    step. if_false.
    assert (MU5 : munch aWL m (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply munch_write; [exact MU4 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM5 : wmono rsegs m (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply wmono_write; exact WM4).
    assert (MI5 : mem_inv rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply mem_inv_store; [exact MI4 | cbn [length]; exact HSe]).
    assert (AJ5 : aJ_on (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]))
      by (apply (aJ_ostore_on m4 (o + 16) (nth 0 row (Z_to_bv 8 0))); [exact AJ4 | exact API | exact ART | lia]).
    assert (FR5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR4 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST5 : stk rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) LO (SP0 + -128))
      by (apply stk_write; [exact ST4 | lia | cbn [length]; lia]).
    assert (P1_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_5 : rw_cells rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_4 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW5 : wr_at rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW4).
    assert (HBy5 : bytes_at rsegs (write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) (o + 12)
                     [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
                      Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)]).
    { change [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
              Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)]
        with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256)] ++ [nth 0 row (Z_to_bv 8 0)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy4 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 4) with (o + 16) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 16)).
    set (m5 := write_to_mem m4 (wa (o + 16)) [nth 0 row (Z_to_bv 8 0)]) in *. clearbody m5.
    pose proof AJ5 as AJ5c. destruct AJ5c as (_ & _ & _ & AO5 & _ & _).
    (* ===== store 6: o + 17 := row[1] (no overflow guard) ===== *)
    step.
    destruct (a_out0 m5 17 AO5 ltac:(lia) ltac:(lia)) as (k6 & RK6 & K06).
    chk0 (o + 17) k6 RK6 K06 (FpSo1 HE (o + 17) ltac:(lia)).
    assert (HSf : store_ok rsegs m5 (wa (o + 17)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m5 (o + 12) (Z.of_nat 6) 5 1%nat HW5 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + 12 + 5) with (o + 17) in H by lia. exact H. }
    step.
    replace (o + 17 + Z.of_nat 0) with (o + 17) by lia.
    rewrite ?em_le1. rewrite (em_byte_zxb (nth 1 row (Z_to_bv 8 0))).
    assert (MU6 : munch aWL m (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply munch_write; [exact MU5 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM6 : wmono rsegs m (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply wmono_write; exact WM5).
    assert (MI6 : mem_inv rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply mem_inv_store; [exact MI5 | cbn [length]; exact HSf]).
    assert (AJ6 : aJ_on (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]))
      by (apply (aJ_ostore_on m5 (o + 17) (nth 1 row (Z_to_bv 8 0))); [exact AJ5 | exact API | exact ART | lia]).
    assert (FR6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR5 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST6 : stk rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) LO (SP0 + -128))
      by (apply stk_write; [exact ST5 | lia | cbn [length]; lia]).
    assert (P1_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P18_6 : rw_cells rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 18)
                      [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))])
      by (apply rw_cells_frame; [exact P18_5 | lia | cbn [length]; lia | cbn [cells_size csize]; right; cbn [length]; lia]).
    assert (HW6 : wr_at rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 12) (Z.of_nat 6))
      by (apply wr_at_write; exact HW5).
    assert (HBy6 : bytes_at rsegs (write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) (o + 12) HDR).
    { change HDR with ([Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
               Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0)] ++ [nth 1 row (Z_to_bv 8 0)]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HBy5 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + 12 + Z.of_nat 5) with (o + 17) by lia. apply bytes_at_write_same; cbn [length]; lia. }
    try fold (wa (o + 17)).
    set (m6 := write_to_mem m5 (wa (o + 17)) [nth 1 row (Z_to_bv 8 0)]) in *. clearbody m6.
    (* ===== reached the ctrl_lay_block argument setup (0x8571c) ===== *)
    simp_regs.
    apply (Hcont _ _ _ m6 MU6 WM6 MI6 AJ6 ST6 FR6 P1_6 P2_6 HBy6 HW6 P18_6).
  Qed.

  (* atail3 with aJ_on / aepi_on. *)
  Lemma atail3_on : forall (x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26
                        u3 u4 u5 u6 : word) (mc : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 BLK] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)) ->
    evtF rsegs RNG aQp_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 LEN) x26 (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85778) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 u3 u4 u5 u6 mc jf
      HE FR ST MU WM MI AJ P1 P2 P3 P4 P5 P6 CLS.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (FpO HE) as FpOc.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_bytes rsegs mc (o + LEN + -2) 2 (repeat (Z_to_bv 8 0) 2) P6) as (_ & HB6 & HW6).
    clear P6.
    (* addi a0,s9,-2 ; add a0,a0,s0 : a0 = o + LEN - 2 *)
    do 2 step.
    replace (LEN + -2 + o) with (o + LEN + -2) by lia.
    (* beqz a0,85810 : not taken (o + LEN - 2 <> 0) *)
    step. unfold_cond. fold_lit_ux. rewrite (unsigned_lit (o + LEN + -2)) by lia.
    replace (o + LEN + -2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    (* bltu a0,s0,85810 : not taken (o <= o + LEN - 2) *)
    step. unfold_cond. rewrite (unsigned_lit (o + LEN + -2)) by lia. rewrite (unsigned_lit o) by lia.
    replace (o + LEN + -2 <? o) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    chk_go (o + LEN + -2) (Z_to_bv 5 12)
      (a_shadow mc o LEN (o + LEN + -2) (LEN - 2) AOm ltac:(lia) ltac:(lia)) (FpSo1 HE (o + LEN + -2) ltac:(lia)) no_extra.
    (* li a2,194 ; addi a1,s9,-1 ; not a3,s0 ; sb a2,0(a0) *)
    assert (HS1 : store_ok rsegs mc (wa (o + LEN + -2)) 1 = true).
    { pose proof (wr_at_store_ok rsegs mc (o + LEN + -2) (Z.of_nat 2) 0 1%nat HW6 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    step. step. step. step.
    replace (o + LEN + -2 + Z.of_nat 0) with (o + LEN + -2) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 194) by lia.
    assert (MU1 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m
                    (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM1 : wmono rsegs m (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply wmono_write; exact WM).
    assert (MI1 : mem_inv rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply mem_inv_store; [exact MI | cbn [length]; exact HS1]).
    assert (AJ1 : aJ_on (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply (aJ_ostore_on mc (o + LEN + -2) (Z_to_bv 8 194)); [exact AJ | exact API | exact ART | lia]).
    assert (FR1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR | lia | cbn [length]; lia
          | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST1 : stk rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) LO (SP0 + -128))
      by (apply stk_write; [exact ST | lia | cbn [length]; lia]).
    assert (HB1 : bytes_at rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + LEN + -2)
                    [Z_to_bv 8 194]) by (apply bytes_at_write_same; cbn [length]; lia).
    assert (HW1 : wr_at rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + LEN + -2) (Z.of_nat 2))
      by (apply wr_at_write; exact HW6).
    assert (P1_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P3_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 12) [CB 6 HDR])
      by (apply rw_cells_frame; [exact P3 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P4_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 18) [CB 32 BLK])
      by (apply rw_cells_frame; [exact P4 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P5_1 : rw_cells rsegs (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) (o + 50)
                     [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply rw_cells_frame; [exact P5 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    try fold (wa (o + LEN + -2)).
    set (m1 := write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]) in *. clearbody m1.
    pose proof AJ1 as AJ1c. destruct AJ1c as (_ & _ & _ & AO1 & _ & _).
    (* bltu a3,a1,85810 (a3 = ~o, a1 = LEN - 1) : not taken (o + LEN - 1 < 2^64) *)
    step. unfold_cond. rewrite (unsigned_lit o) by lia. rewrite (zb_lxor_ones o) by lia.
    rewrite (unsigned_lit (18446744073709551615 - o)) by lia. rewrite (unsigned_lit (LEN + -1)) by lia.
    replace (18446744073709551615 - o <? LEN + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    (* add a0,s0,a1 : a0 = o + LEN - 1 *)
    step.
    replace (o + (LEN + -1)) with (o + LEN + -1) by lia.
    chk_go (o + LEN + -1) (Z_to_bv 5 12)
      (a_shadow m1 o LEN (o + LEN + -1) (LEN - 1) AO1 ltac:(lia) ltac:(lia)) (FpSo1 HE (o + LEN + -1) ltac:(lia)) no_extra.
    (* li a1,-22 ; sb a1,0(a0) *)
    assert (HS2 : store_ok rsegs m1 (wa (o + LEN + -1)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m1 (o + LEN + -2) (Z.of_nat 2) 1 1%nat HW1 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + LEN + -2 + 1) with (o + LEN + -1) in H by lia.
      exact H. }
    step. step.
    replace (o + LEN + -1 + Z.of_nat 0) with (o + LEN + -1) by lia.
    rewrite ?em_le1. rewrite em_byte_m22.
    assert (MU2 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m
                    (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply munch_write; [exact MU1 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM2 : wmono rsegs m (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply wmono_write; exact WM1).
    assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply mem_inv_store; [exact MI1 | cbn [length]; exact HS2]).
    assert (AJ2 : aJ_on (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply (aJ_ostore_on m1 (o + LEN + -1) (Z_to_bv 8 234)); [exact AJ1 | exact API | exact ART | lia]).
    assert (FR2 : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply rw_cells_frame; [exact FR1 | lia | cbn [length]; lia
          | cbn [cells_size csize Nat.add length]; lia]).
    assert (ST2 : stk rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) LO (SP0 + -128))
      by (apply stk_write; [exact ST1 | lia | cbn [length]; lia]).
    assert (HBF : bytes_at rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + LEN + -2)
                    [Z_to_bv 8 194; Z_to_bv 8 234]).
    { change [Z_to_bv 8 194; Z_to_bv 8 234] with ([Z_to_bv 8 194] ++ [Z_to_bv 8 234]).
      apply bytes_at_app. split.
      - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | left; cbn [length]; lia].
      - cbn [length]. replace (o + LEN + -2 + Z.of_nat 1) with (o + LEN + -1) by lia.
        apply bytes_at_write_same; cbn [length]; lia. }
    assert (P1' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) o [CB 6 db])
      by (apply rw_cells_frame; [exact P1_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P2' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 6) [CB 6 sb])
      by (apply rw_cells_frame; [exact P2_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P3' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 12) [CB 6 HDR])
      by (apply rw_cells_frame; [exact P3_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P4' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 18) [CB 32 BLK])
      by (apply rw_cells_frame; [exact P4_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    assert (P5' : rw_cells rsegs (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply rw_cells_frame; [exact P5_1 | lia | cbn [length]; lia | cbn [cells_size csize]; lia]).
    try fold (wa (o + LEN + -1)).
    set (m2 := write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]) in *.
    assert (RReq : (if EE then LEN else 0) = LEN) by (rewrite HE; reflexivity).
    pose proof AJ2 as AJ2c. destruct AJ2c as (AC2 & SW2 & AW2 & AO2 & FP2 & TL2).
    eapply aepi_on.
    - symmetry; exact RReq.
    - lia.
    - exact FR2.
    - exact ST2.
    - rewrite RReq. exact MU2.
    - exact WM2.
    - exact MI2.
    - exact AC2.
    - exact SW2.
    - exact AW2.
    - rewrite RReq. exact FP2.
    - intros _. unfold aRES. split; [|split].
      + exact (em_fr_bytes rsegs m2 o LEN db sb BLK (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0))
                 (nth 1 row (Z_to_bv 8 0)) P1' P2' P3' P4' P5' HBF ltac:(lia)).
      + intros HL2. exact (em_E_wok _ _ _ _ HE HL2).
      + exact CLS.
  Qed.

  (* atail2 with aJ_on and HFN_on (ctrl_finish_contract_F_on has no shadow premise). *)
  Lemma atail2_on : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26
                        u3 u4 u5 u6 : word) (mc : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    bytes_at rsegs mc f row -> addressable mc (f + 18) 3 ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 LB] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aQp_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 LEN) x26 (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8576c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 u3 u4 u5 u6 mc jf
      HE FR ST MU WM MI AJ HRf ADf3 P1 P2 P3 P4 P5 P6.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    pose proof Dsf as Dsfu. unfold ly_dj in Dsfu.
    pose proof FPm as FPm2. destruct FPm2 as (DT & TS & C & T & DB & kk & _ & _ & _ & _ & _ & _ & FSlo & _).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as R18.
    pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as R20.
    assert (Hrn : 0 <= RO) by (unfold ubat; lia).
    assert (Hcn : 0 <= CC <= 2) by (unfold ubat in Hc |- *; lia).
    (* mv a0,s0 ; mv a1,s1 ; jal ctrl_finish *)
    step. step. step.
    eapply evtF_cut.
    { eapply HFN_on with (p := o) (f := f) (c := CC) (o := RO) (n := RL) (lo := LO) (row := row) (B := LB).
      - reflexivity.
      - reflexivity.
      - exact Hf8.
      - exact Hf24.
      - exact Hrl.
      - exact HRf.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Hc.
      - exact Hc2.
      - exact Ho.
      - lia.
      - intros _; exact P4.
      - rewrite Esp; exact ST.
      - rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - rewrite Esp; lia.
      - intros _; rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - exact ACm.
      - exact ADf3.
      - intros _; exact (addressable_sub mc o LEN 18 32 AOm ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros x Hx. rewrite Esp. cbn [outside]. split.
        + unfold RT_LO, RT_HI, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
            CTRL_FINISH_FRAME in Hx, FSlo |- *; unfold HIGHMEM_BEG in HHM.
          destruct Hx as [HRt|HSt]; lia.
        + apply (em_fin_sub CC RO RL o Hc Hrn Hc2). cbn [outside]. split; [|exact I].
          destruct Hx as [HRt|HSt].
          * unfold RT_LO, RT_HI in ART, HRt |- *; lia.
          * pose proof (app_ivl_meta o (o + LEN) x API HSt) as Hm2; lia.
      (* the footprint premises of ctrl_finish_contract_F *)
      - rewrite Esp. eapply rng_sub; [exact FpWIN | unfold CTRL_FINISH_FRAME; lia | unfold CTRL_FINISH_FRAME; lia].
      - eapply rng_sub; [exact FpIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia].
      - exact FpROW.
      - exact (dcF_shadowspan RNG ASAN_K f (f + 23) (f + 18) (f + 20)
                 (FpSfK f (f + 23) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros _. split.
        + eapply rng_sub; [exact (FpO HE) | lia | lia].
        + exact (dcF_shadowspan RNG ASAN_K o (o + LEN - 1) (o + 18) (o + 49)
                   (FpSoK HE o (o + LEN - 1) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' (t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & -> & MU1 & WM1 & MI1 & ST1 & HF).
    fixret. rewrite Esp in MU1, ST1.
    pose proof (MI1 MI) as MIm1.
    assert (SUBw : sub_fp ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o) aWL).
    { intros x Hx. apply (em_fin_sub2 CC RO RL o (SP0 + -128 - 32, SP0 + -128) Hc Hrn Hc2).
      cbn [outside] in Hx |- *. destruct Hx as (HAx & HBx & _). split; [lia | split; [lia | exact I]]. }
    assert (MU1' : munch [(SP0 + -128 - 32, SP0 + -128); (o + 18, o + 50)] mc m1)
      by (apply (munch_weaken _ _ mc m1 (em_fin_sub2 CC RO RL o (SP0 + -128 - 32, SP0 + -128) Hc Hrn Hc2)); exact MU1).
    assert (MUf : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m1).
    { apply (munch_trans _ m mc m1 MU).
      apply (munch_weaken ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
      intros x Hx. apply SUBw. cbn [outside app] in Hx |- *. tauto. }
    assert (WMf : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc m1 WM WM1)).
    assert (AJm1 : aJ_on m1).
    { apply (aJ_wout_on ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o) mc m1 API ART AJ MU1 WM1 SUBw).
      intros x Hx. assert (xLO : x < LO) by lia.
      destruct (Z.eq_dec CC 0) as [C0|C0].
      - left. rewrite C0. cbn [fin_w outside]. split; [lia | exact I].
      - destruct (Z_lt_le_dec x (o + 18)) as [L1|L1].
        + left. cbn [outside]. split;
            [lia | apply (em_fin_sub CC RO RL o Hc Hrn Hc2); cbn [outside]; split; [lia | exact I]].
        + destruct (Z_lt_le_dec x (o + 50)) as [L2|L2].
          * right. destruct (HF ltac:(lia)) as (HB4 & _ & _).
            destruct (em_rw_bytes rsegs m1 (o + 18) 32 (fin CC RO RL LB) HB4) as (HL4 & (_ & _ & HBf) & _).
            pose proof (HBf (Z.to_nat (x - (o + 18)))) as HM4. rewrite HL4 in HM4.
            specialize (HM4 ltac:(lia)).
            replace (o + 18 + Z.of_nat (Z.to_nat (x - (o + 18)))) with x in HM4 by lia.
            destruct (nth_error (fin CC RO RL LB) (Z.to_nat (x - (o + 18)))) as [b|] eqn:EN.
            -- exists b. exact HM4.
            -- apply nth_error_None in EN. rewrite HL4 in EN. lia.
          * left. cbn [outside]. split;
              [lia | apply (em_fin_sub CC RO RL o Hc Hrn Hc2); cbn [outside]; split; [lia | exact I]]. }
    assert (FRm1 : rw_cells rsegs m1 (SP0 + -128)
                     [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                      C8 s2; C8 s1; C8 s0; C8 ra])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1' WM1);
          cbn [disjoint_from cells_size csize Nat.add length]; lia).
    assert (P1' : rw_cells rsegs m1 o [CB 6 db])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P1 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P2' : rw_cells rsegs m1 (o + 6) [CB 6 sb])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P2 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P3' : rw_cells rsegs m1 (o + 12) [CB 6 HDR])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P3 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P5' : rw_cells rsegs m1 (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P5 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P6' : rw_cells rsegs m1 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)])
      by (apply (rw_cells_transport rsegs _ mc m1 _ _ P6 MU1' WM1);
          cbn [disjoint_from cells_size csize]; lia).
    assert (P4' : rw_cells rsegs m1 (o + 18) [CB 32 BLK]).
    { destruct (Z.eq_dec CC 0) as [C0|C0].
      - assert (BLKeq : BLK = LB) by (unfold fin; rewrite C0; reflexivity).
        rewrite BLKeq.
        assert (MUw : munch [(SP0 + -128 - 32, SP0 + -128)] mc m1).
        { apply (munch_weaken ((SP0 + -128 - 32, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
          rewrite C0. cbn [fin_w]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
        apply (rw_cells_transport rsegs [(SP0 + -128 - 32, SP0 + -128)] mc m1 _ _ P4 MUw WM1);
          cbn [disjoint_from cells_size csize]; lia.
      - destruct (HF ltac:(lia)) as (HB4 & _ & _). exact HB4. }
    assert (CLS' : CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).
    { intros HCC. destruct (HF HCC) as (_ & CL1 & CL2). split; [exact CL1 | exact CL2]. }
    eapply (atail3_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 jf);
      [ exact HE | exact FRm1 | exact ST1 | exact MUf | exact WMf | exact MIm1 | exact AJm1
      | exact P1' | exact P2' | exact P3' | exact P4' | exact P5' | exact P6' | exact CLS' ].
  Qed.

  (* alay_ret with aJ_on (stretch 3 of the glue). *)
  Lemma alay_ret_on : forall (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w0 : word)
      (m1 : word -> option byte),
    EE = true ->
    rw_cells rsegs m1 (SP0 + -128)
      (C8 w0 :: C8 (Z_to_bv 64 g) :: C8 (Z_to_bv 64 ns) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs m1 LO (SP0 + -128) ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 -> aJ_on m1 ->
    bytes_at rsegs m1 f row -> addressable m1 f 24 ->
    rw_cells rsegs m1 o [CB 6 db] -> rw_cells rsegs m1 (o + 6) [CB 6 sb] ->
    rw_cells rsegs m1 (o + 12) [CB 6 HDR] -> rw_cells rsegs m1 (o + 18) [CB 32 LB] ->
    rw_cells rsegs m1 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs m1 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aQp_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp t0' t1' t2'
               (Z_to_bv 64 o) (Z_to_bv 64 f) a0' a1' a2' a3' a4' a5' a6' a7'
               (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) t3' t4' t5' t6')
          F (Z_to_bv 64 0x85730) fc None m1 (seg_rom rsegs)).
  Proof.
    intros x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w0 m1
      HE FR1 ST1 MUtot WMtot MIm1 AJ1 HRf1 Af1 P1' P2' P3' LAY P5' P6'.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof Af as Afb. destruct Afb as (Hfge & _ & _ & _).
    pose proof Amd as Amdb. destruct Amdb as (Hmdge & _ & _ & _).
    pose proof AJ1 as AJ1c. destruct AJ1c as (ACm1 & SWm1 & AWm1 & AOm1 & FPm1 & TLm1).
    pose proof (addressable_app m1 o LEN AOm1) as AIo.
    destruct (AO HE) as (AOaddr & AOend & ART).
    destruct (HEo HE) as (HOrw & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (ADf3 : addressable m1 (f + 18) 3)
      by (exact (addressable_sub m1 f 24 18 3 Af1 ltac:(lia) ltac:(lia) ltac:(lia))).
    (* 0x85730: addi a0,s1,23 ; the checked read of row[23] (the byte f + 23 is in the addressable row) *)
    pose proof (rd_byte rsegs m1 f row 23 HRf1 ltac:(lia)) as RD23. change (Z.of_nat 23) with 23 in RD23.
    pose proof (byte_range (nth 23 row (Z_to_bv 8 0))) as R23.
    step.
    chk_go (f + 23) (Z_to_bv 5 12) (a_shadow m1 f 24 (f + 23) 23 Af1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 23) ltac:(lia)) no_extra.
    (* lbu a0,0(a0) ; ld a4,16(sp) ; beqz a0,0x8576c *)
    step. step. step.
    rewrite (rc_u8_eqb row 23 0) by lia.
    pose proof (rc_u8_range row 23) as R23u.
    destruct (Z.eqb_spec (rc_u8 row 23) 0) as [A0|A0]; cbv iota.
    - (* row[23] = 0: straight to the ctrl_finish call *)
      eapply atail2_on with (mc := m1) (jf := le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns));
        [ exact HE | exact (arw_cb3' m1 _ _ _ _ _ FR1) | exact ST1 | exact MUtot | exact WMtot | exact MIm1
        | exact AJ1 | exact HRf1 | exact ADf3 | exact P1' | exact P2' | exact P3' | exact LAY | exact P5'
        | exact P6' ].
    - (* row[23] = 1: the guard (o < 2^64 - 50), then reac_braid_encode(o + 50, n, w0, n, ns) with ns <= 0 *)
      assert (A1 : AA = 1) by (pose proof HA as HA'; unfold ubat in HA' |- *; unfold rc_u8 in A0, R23u; lia).
      step. step. unfold_cond. rewrite (unsigned_lit o) by lia.
      change (bv_unsigned (Z_to_bv 64 (-50))) with 18446744073709551566.
      replace (o <? 18446744073709551566) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
      do 5 step.
      eapply evtF_cut.
      { eapply HBR with (ns := ns); [pose proof (Hns0 A1); lia | reflexivity | |].
        - rewrite Esp. unfold REAC_BRAID_ENCODE_FRAME.
          destruct (stk_split rsegs m1 LO (SP0 + -128 - 128) (SP0 + -128) ST1 ltac:(lia)) as (_ & STb).
          exact STb.
        - rewrite Esp. unfold REAC_BRAID_ENCODE_FRAME. eapply rng_sub; [exact FpWIN | lia | lia]. }
      intros ms' (m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite Esp in MU2, ST2. unfold REAC_BRAID_ENCODE_FRAME in MU2, ST2.
      fixret.
      assert (WB : sub_fp [(SP0 + -128 - 128, SP0 + -128)] [(LO, SP0)])
        by (intros x Hx; cbn [outside] in *; destruct Hx as [H1 _]; split; [lia | exact I]).
      assert (AJ2 : aJ_on m2) by (exact (aJ_win_on _ m1 m2 AJ1 MU2 WM2 WB)).
      assert (MUtot2 : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m2).
      { apply (munch_trans _ m m1 m2 MUtot).
        apply (munch_weaken [(SP0 + -128 - 128, SP0 + -128)]); [|exact MU2].
        intros x Hx. cbn [outside app] in Hx. destruct Hx as (H1 & _). cbn [outside]. split; [lia | exact I]. }
      assert (WMtot2 : wmono rsegs m m2) by (exact (wmono_trans rsegs m m1 m2 WMtot WM2)).
      pose proof (MI2 MIm1) as MIm2.
      assert (ST2' : stk rsegs m2 LO (SP0 + -128)).
      { destruct (stk_split rsegs m1 LO (SP0 + -128 - 128) (SP0 + -128) ST1 ltac:(lia)) as (STa & _).
        pose proof (stk_transport_disjoint rsegs _ m1 m2 LO (SP0 + -128 - 128) STa MU2 WM2
                      ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STa2.
        exact (stk_merge rsegs m2 LO (SP0 + -128 - 128) (SP0 + -128) STa2 ST2 ltac:(lia)). }
      assert (FR2 : rw_cells rsegs m2 (SP0 + -128)
                      (C8 w0 :: C8 (Z_to_bv 64 g) :: C8 (Z_to_bv 64 ns) ::
                       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
                       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]))
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2);
            cbn [disjoint_from cells_size csize Nat.add length]; lia).
      assert (P1'' : rw_cells rsegs m2 o [CB 6 db])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P1' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P2'' : rw_cells rsegs m2 (o + 6) [CB 6 sb])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P2' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P3'' : rw_cells rsegs m2 (o + 12) [CB 6 HDR])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P3' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P4'' : rw_cells rsegs m2 (o + 18) [CB 32 LB])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ LAY MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P5'' : rw_cells rsegs m2 (o + 50)
                       [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P5' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (P6'' : rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)])
        by (apply (rw_cells_transport rsegs _ m1 m2 _ _ P6' MU2 WM2);
            cbn [disjoint_from cells_size csize]; split; [djl DsoLO | exact I]).
      assert (HRf2 : bytes_at rsegs m2 f row)
        by (apply (bytes_at_transport rsegs _ m1 m2 f row HRf1 MU2); rewrite Hrl;
            cbn [disjoint_from]; split; [djl Dsf | exact I]).
      assert (ADf3' : addressable m2 (f + 18) 3)
        by (exact (fl_addressable _ m1 m2 (f + 18) 3 ADf3 MU2 (fun x Hx => fl_shadow_out _ LO SP0 x WB HHM Hx))).
      eapply atail2_on with (mc := m2) (jf := le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns));
        [ exact HE | exact (arw_cb3' m2 _ _ _ _ _ FR2) | exact ST2' | exact MUtot2 | exact WMtot2 | exact MIm2
        | exact AJ2 | exact HRf2 | exact ADf3' | exact P1'' | exact P2'' | exact P3'' | exact P4'' | exact P5''
        | exact P6'' ].
  Qed.

  (* aKont with aJ_on. *)
  Definition aKont_on : Prop :=
    forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word) (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    bytes_at rsegs mc (o + 12) HDR -> wr_at rsegs mc (o + 12) (Z.of_nat 6) ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs)).

  (* aMS with aKont_on. *)
  Definition aMS_on : Prop :=
    forall (t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aKont_on -> EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x855a8) fc None mc (seg_rom rsegs)).

  (* aent_g2 with atr_on / aepi0_on / HQK0_on. *)
  Lemma aent_g2_on : forall (t0 t1 t2 x10 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS_on -> aKont_on -> (LL = 2 \/ em_wok n = true) ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10
               (zxb (nth 21 row (Z_to_bv 8 0))) (Z_to_bv 64 0) x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x8553c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x10 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK HW FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    pose proof (atr_on _ mc MU WM (ain_sub LO ltac:(lia))) as (AC1 & SW1 & FP1 & ADT).
    pose proof (ADT _ _ Af) as ADfc. pose proof (ADT _ _ Amd) as ADmc.
    pose proof (em_obj0 rsegs m mc _ _ f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 22 HRc ltac:(lia)) as RD22. change (Z.of_nat 22) with 22 in RD22.
    (* addi a0,s1,22 ; the instrumented check of the byte f + 22 (its slow path writes a6) *)
    step.
    chk_go (f + 22) (Z_to_bv 5 16) (a_shadow mc f 24 (f + 22) 22 ADfc ltac:(lia) ltac:(lia)) (FpSf1 (f + 22) ltac:(lia)) no_extra.
    (* lbu a0,0(a0) ; li a3,1 ; bne a0,a3,85580 *)
    step. step. step.
    pose proof (rc_u8_range row 22) as R22.
    rewrite (rc_u8_eqb row 22 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 22) 1) as [G1|G1]; cbn [negb]; cbv iota.
    - (* GG = 1: andi a0,s6,7 ; bnez a0,85810 : not taken (md mod 8 = 0) *)
      step.
      replace (Z.land (bv_unsigned (Z_to_bv 64 md)) 7) with 0
        by (rewrite unsigned_lit by lia; rewrite rc_land7; symmetry; exact Hmd8).
      step. if_false.
      (* addi a0,s6,56 ; the instrumented check of the 4-byte word md + 56 (its slow path writes a6) *)
      step.
      chk_go (md + 56) (Z_to_bv 5 16)
        (a_shadow4 mc md 296 (md + 56) 56 ADmc ltac:(lia) ltac:(lia) ltac:(rlia) ltac:(lia)) (FpSmd1 (md + 56) ltac:(lia)) add3.
      pose proof (em_obj0 rsegs m mc _ _ md mb 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm) as HMc.
      destruct (rc_rd4_opaque rsegs mc md mb 56 HMc ltac:(lia)) as (L4 & EL4 & RD56).
      change (Z.of_nat 56) with 56 in RD56.
      (* lw a0,0(a0) ; beqz a0,85808 *)
      step. rewrite (em_lw_hid mb L4 EL4).
      step. pose proof (em_hid_range mb) as RH. rewrite em_eqb0 by lia.
      destruct (Z.eqb_spec (em_hid mb) 0) as [H0|H0]; cbv iota.
      + (* 0x85808 : li s9,0 ; j 857c8 ; the early return *)
        step. step.
        assert (HEF : EE = false) by (apply em_E_false_g; assumption).
        eapply evtF_mono;
          [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
      + (* 0x85580 : mv a0,s4 ; beqz a2,855a8 : taken (a2 = 0) *)
        step. step. if_true.
        eapply KMS; [exact HK | apply em_E_true; [exact HW | right; exact H0] | eassumption ..].
    - (* GG <> 1: 0x85580 : mv a0,s4 ; beqz a2,855a8 : taken (a2 = 0) *)
      step. step. if_true.
      eapply KMS; [exact HK | apply em_E_true; [exact HW | left; exact G1] | eassumption ..].
  Qed.

  (* aent_nchk with aent_g2_on. *)
  Lemma aent_nchk_on : forall (t0 t1 t2 x10 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS_on -> aKont_on -> LL <> 2 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x85470) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x10 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK L2 FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    (* addiw a0,s4,-41 ; li a2,-39 ; li s9,0 ; bltu a0,a2,857c8 *)
    do 4 step. rewrite em_wok_ltu by lia.
    destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
    - (* andi a0,s4,1 ; bnez a0,857c8 *)
      step. step. rewrite em_odd by lia.
      destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
      + (* beqz s6,85494 : not taken (md <> 0) ; li a2,0 ; j 8553c *)
        step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
        cbv iota. step. step.
        eapply aent_g2_on; [exact KMS | exact HK | right | eassumption ..].
        unfold em_wok. rewrite Ev. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia).
        replace (n <=? 40) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + assert (HEF : EE = false)
          by (apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]).
        eapply evtF_mono;
          [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
              by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
              by (symmetry; apply Z.leb_gt; lia); reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
    - assert (HEF : EE = false)
        by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
              by (symmetry; apply Z.leb_gt; lia); reflexivity]).
      eapply evtF_mono;
        [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
  Qed.

  (* aent_g1 with aent_g2_on / aent_nchk_on. *)
  Lemma aent_g1_on : forall (t0 t1 t2 x11 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aMS_on -> aKont_on ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 (f + 21))
               x11 x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x8543c) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x11 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j KMS HK FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof Amd as (Hma & _ & HmE & _). unfold APPMEM_END in HmE.
    pose proof (em_obj0 rsegs m mc _ _ f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 21 HRc ltac:(lia)) as RD21. change (Z.of_nat 21) with 21 in RD21.
    (* lbu a1,0(a0) ; li a0,2 ; beq a1,a0,85488 *)
    step. step. step.
    pose proof (rc_u8_range row 21) as R21.
    rewrite (rc_u8_eqb row 21 2) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbv iota.
    - (* LL = 2: beqz s6,85494 : not taken (md <> 0) ; li a2,0 ; j 8553c *)
      step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
      cbv iota. step. step.
      eapply aent_g2_on; [exact KMS | exact HK | left; exact L2 | eassumption ..].
    - (* bnez a1,85464 *)
      step. rewrite (rc_u8_eqb row 21 0) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 0) as [L0|L0]; cbn [negb]; cbv iota.
      + (* LL = 0: the n check at 0x8544c (addiw ; li a2,-39 ; li s9,0 ; bltu) *)
        do 4 step. rewrite em_wok_ltu by lia.
        destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
        * step. step. rewrite em_odd by lia.
          destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
          -- (* 0x85464 : bnez s6,85470 : taken (md <> 0) *)
             step. rewrite rc_eqb by lia.
             replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
             eapply aent_nchk_on; [exact KMS | exact HK | exact L2 | eassumption ..].
          -- assert (HEF : EE = false)
               by (apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]).
             eapply evtF_mono;
               [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
                  by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
                  by (symmetry; apply Z.leb_gt; lia); reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
        * assert (HEF : EE = false)
            by (apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
                  by (symmetry; apply Z.leb_gt; lia); reflexivity]).
          eapply evtF_mono;
            [ eapply aepi0_on; [exact HEF | eassumption ..] | intros ms_ HP_; exact (HQK0_on ms_ HEF HP_) ].
      + (* LL = 1: 0x85464 : bnez s6,85470 : taken (md <> 0) *)
        step. rewrite rc_eqb by lia.
        replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
        eapply aent_nchk_on; [exact KMS | exact HK | exact L2 | eassumption ..].
  Qed.

  (* aent_mc with aJ_on and HMC_on (each call's region by ae_srw_mc). *)
  Lemma aent_mc_on : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x21 u3 u4 u5 u6 w0 : word)
      (mc : word -> option byte),
    aKont_on -> EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc -> wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB (Z.to_nat LEN) (repeat (Z_to_bv 8 0) (Z.to_nat LEN))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) x10 x11 x12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               x21 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x85628) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 x21 u3 u4 u5 u6 w0 mc HK HE FR ST MU WM MI AJ RW0.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (AOo & APo & ART).
    destruct (HEo HE) as (_ & DsoLO & _ & _ & _ & _ & Dod & Dos & _).
    unfold ly_dj in DsoLO.
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (Eo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    (* split the zeroed output: o, o + 6, o + 12 (6 bytes each) and o + 18 (LEN - 18 bytes) *)
    destruct (em_rw_rep rsegs mc o (Z_to_bv 8 0) (Z.to_nat LEN) 6 RW0 ltac:(lia)) as (P1z & R1).
    destruct (em_rw_rep rsegs mc _ (Z_to_bv 8 0) _ 6 R1 ltac:(lia)) as (P2z & R2).
    destruct (em_rw_rep rsegs mc _ (Z_to_bv 8 0) _ 6 R2 ltac:(lia)) as (P3z & P4z).
    replace (o + Z.of_nat 6) with (o + 6) in P2z by lia.
    replace (o + Z.of_nat 6 + Z.of_nat 6) with (o + 12) in P3z by lia.
    replace (o + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 6) with (o + 18) in P4z by lia.
    replace (Z.to_nat LEN - 6 - 6 - 6)%nat with (Z.to_nat (LEN - 18)) in P4z by lia.
    clear RW0 R1 R2.
    (* local copies of the facts the two checked_memcpy need *)
    pose proof (bytes_at_bound rsegs m d db HD) as BDb. rewrite Hdb in BDb. change (Z.of_nat 6) with 6 in BDb.
    pose proof (bytes_at_bound rsegs m s sb HSb) as BSb. rewrite Hsb in BSb. change (Z.of_nat 6) with 6 in BSb.
    pose proof APD as APDl. pose proof APS as APSl. pose proof HAE as HAEl.
    pose proof Dsd as Dsdl. unfold ly_dj in Dsdl.
    pose proof Dss as Dssl. unfold ly_dj in Dssl.
    pose proof Dod as Dodl. unfold ly_dj in Dodl.
    pose proof Dos as Dosl. unfold ly_dj in Dosl.
    assert (Ed : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by (apply unsigned_lit; lia).
    (* route (C): the first memcpy call's shadow region, from aJ_on's transport and HSW_on *)
    assert (SWc1 : shadow_rw_on (asan_memcpy_shadow_R (Z_to_bv 64 o) (Z_to_bv 64 d) (Z_to_bv 64 6)) mc)
      by (exact (ae_srw_mc mc _ _ _ o d Eo Ed E6 HE ltac:(lia) ltac:(lia) (or_introl eq_refl) SWm)).
    assert (MKm : meta_kept m mc).
    { apply (munch_meta aWL m mc MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (ADd1 : addressable mc d 6) by (apply (addressable_kept m mc d 6 Ad MKm)).
    assert (ADo1 : addressable mc o 6) by (apply (addressable_prefix mc o LEN 6 AOm); lia).
    assert (HDc1 : bytes_at rsegs mc d db).
    { apply (em_obj rsegs m mc LO SP0 o LEN d db 6 MU HD ltac:(rewrite Hdb; reflexivity));
        [ exact Dsd | exact Dod ]. }
    (* li a2,6 ; li s5,6 ; mv a0,s0 ; mv a1,s7 ; jal checked_memcpy(o, d, 6) *)
    do 5 step.
    pose proof HMC_on as HMc1.
    unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K,
      rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMc1.
    cbv zeta in HMc1.
    (* the footprint premises of asan_memcpy_contract_F_on for this call, asserted here so that the premise search
       below is pure [exact] (a failing lia inside [first] case-splits on the apartness facts in the context) *)
    assert (FpWc1 : rng RNG (SP0 + -128 - 2224) 2224) by (eapply rng_sub; [exact FpWIN | lia | lia]).
    assert (FpOc1 : rng RNG o 6) by (eapply rng_sub; [exact (FpO HE) | lia | lia]).
    assert (FpIMGc : rng RNG IMG_LO (IMG_HI - IMG_LO))
      by (eapply rng_sub; [exact FpIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia]).
    assert (FpCVw : rng RNG (shadow_addr (SP0 + -128 - 2224) / 8 * 8)
                      (shadow_addr (SP0 + -128 - 2224 + 2224 - 1) / 8 * 8 + 8
                       - shadow_addr (SP0 + -128 - 2224) / 8 * 8))
      by (unfold shadow_addr;
          exact (FpWSH (SP0 + -128 - 2224) (SP0 + -128 - 2224 + 2224 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVo1 : rng RNG (shadow_addr o / 8 * 8)
                       (shadow_addr (o + 6 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8))
      by (unfold shadow_addr; exact (FpSoK HE o (o + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVd1 : rng RNG (shadow_addr d / 8 * 8)
                       (shadow_addr (d + 6 - 1) / 8 * 8 + 8 - shadow_addr d / 8 * 8))
      by (unfold shadow_addr; exact (FpSdK d (d + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    eapply evtF_cut.
    { eapply HMc1 with (src := db) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO); rewrite ?Esp, ?Eo, ?Ed, ?E6;
      first
        [ exact HDc1
        | rewrite Hdb; reflexivity
        | exact P1z
        | exact ADd1
        | exact ADo1
        | exact ST
        | exact HHM
        | exact ACm
        | exact SWc1
        | exact MI
        | right; exact (proj1 APDl)
        | right; apply API; lia
        | right; split; [ exact (proj2 APDl) | apply API; lia ]
        | (* footprint: pre-asserted below, so the search runs no lia *)
          exact FpRB | exact FpIMGc | exact FpWc1 | exact FpOc1 | exact FpD
        | right; exact FpCVo1 | right; exact FpCVd1 | right; exact FpCVw
        | lia ]. }
    intros ms2 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SW2).
    rewrite Esp, Eo, E6 in MU2. rewrite Esp in ST2. rewrite Eo, E6 in RW2.
    change (Z.to_nat 6) with 6%nat in RW2, MU2.
    fixret.
    assert (MU2f : munch aWL m m2).
    { apply (munch_trans _ m mc m2 MU).
      apply (munch_weaken [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)]); [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (WM2f : wmono rsegs m m2) by (exact (wmono_trans rsegs m mc m2 WM WM2)).
    assert (SUBw2 : sub_fp [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ2 : aJ_on m2).
    { apply (aJ_wout_on [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 API ART AJ MU2 WM2 SUBw2).
      intros x Hx.
      destruct (Z_lt_le_dec x o) as [Lx|Lx]; [left; cbn [outside]; split; [lia | split; [lia | exact I]]|].
      destruct (Z_lt_le_dec x (o + 6)) as [Lx2|Lx2].
      - right. destruct (em_rw_bytes rsegs m2 o 6 db RW2) as (_ & HBo2 & _). destruct HBo2 as (_ & _ & HBf2).
        pose proof (HBf2 (Z.to_nat (x - o)) ltac:(rewrite Hdb; lia)) as HMr2.
        replace (o + Z.of_nat (Z.to_nat (x - o))) with x in HMr2 by lia.
        destruct (nth_error db (Z.to_nat (x - o))) as [bb|] eqn:EN;
          [ exists bb; exact HMr2 | apply nth_error_None in EN; rewrite Hdb in EN; lia ].
      - left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (MKm2 : meta_kept m m2).
    { apply (munch_meta aWL m m2 MU2f). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (FR2 : rw_cells rsegs m2 (SP0 + -128)
                    [CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)); C8 s11; C8 s10; C8 s9; C8 s8;
                     C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ FR MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P2' : rw_cells rsegs m2 (o + 6) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P2z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3' : rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P3z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4' : rw_cells rsegs m2 (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] mc m2 _ _ P4z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    (* addi a0,s0,6 ; bgeu s5,a0,85810 : not taken (6 < o + 6, no wrap) *)
    assert (Eo6 : bv_unsigned (Z_to_bv 64 (o + 6)) = o + 6) by (apply unsigned_lit; lia).
    step. step. if_false.
    (* checked_memcpy(o + 6, s, 6) *)
    pose proof AJ2 as AJ2c. destruct AJ2c as (AC2x & SW2x & AW2x & AO2 & FP2x & TL2x).
    assert (Es : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    (* route (C): the second memcpy call's shadow region *)
    assert (SWc2 : shadow_rw_on (asan_memcpy_shadow_R (Z_to_bv 64 (o + 6)) (Z_to_bv 64 s) (Z_to_bv 64 6)) m2)
      by (exact (ae_srw_mc m2 _ _ _ (o + 6) s Eo6 Es E6 HE ltac:(lia) ltac:(lia) (or_intror eq_refl) SW2x)).
    assert (ADs2 : addressable m2 s 6) by (apply (addressable_kept m m2 s 6 As MKm2)).
    assert (ADo6 : addressable m2 (o + 6) 6) by (apply (addressable_sub m2 o LEN 6 6 AO2); lia).
    assert (HSc2 : bytes_at rsegs m2 s sb).
    { apply (em_obj rsegs m m2 LO SP0 o LEN s sb 6 MU2f HSb ltac:(rewrite Hsb; reflexivity));
        [ exact Dss | exact Dos ]. }
    (* li a2,6 ; mv a1,s8 ; jal checked_memcpy *)
    do 3 step.
    pose proof HMC_on as HMc2.
    unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K,
      rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMc2.
    cbv zeta in HMc2.
    (* the footprint premises of this call (as at the first copy: pure [exact] in the search below) *)
    assert (FpOc2 : rng RNG (o + 6) 6) by (eapply rng_sub; [exact (FpO HE) | lia | lia]).
    assert (FpCVo2 : rng RNG (shadow_addr (o + 6) / 8 * 8)
                       (shadow_addr (o + 6 + 6 - 1) / 8 * 8 + 8 - shadow_addr (o + 6) / 8 * 8))
      by (unfold shadow_addr; exact (FpSoK HE (o + 6) (o + 6 + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (FpCVs2 : rng RNG (shadow_addr s / 8 * 8)
                       (shadow_addr (s + 6 - 1) / 8 * 8 + 8 - shadow_addr s / 8 * 8))
      by (unfold shadow_addr; exact (FpSsK s (s + 6 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
    eapply evtF_cut.
    { eapply HMc2 with (src := sb) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO); rewrite ?Esp, ?Eo6, ?Es, ?E6;
      first
        [ exact HSc2
        | rewrite Hsb; reflexivity
        | exact P2'
        | exact ADs2
        | exact ADo6
        | exact ST2
        | exact HHM
        | exact AC2
        | exact SWc2
        | exact MI2
        | right; exact (proj1 APSl)
        | right; apply API; lia
        | right; split; [ exact (proj2 APSl) | apply API; lia ]
        | (* footprint: pre-asserted below, so the search runs no lia *)
          exact FpRB | exact FpIMGc | exact FpWc1 | exact FpOc2 | exact FpS
        | right; exact FpCVo2 | right; exact FpCVs2 | right; exact FpCVw
        | lia ]. }
    intros ms3 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & RW3 & BD3 & AC3 & SW3).
    rewrite Esp, Eo6, E6 in MU3. rewrite Esp in ST3. rewrite Eo6, E6 in RW3.
    change (Z.to_nat 6) with 6%nat in RW3, MU3.
    fixret.
    assert (MU3f : munch aWL m m3).
    { apply (munch_trans _ m m2 m3 MU2f).
      apply (munch_weaken [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)]); [|exact MU3].
      intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (WM3f : wmono rsegs m m3) by (exact (wmono_trans rsegs m m2 m3 WM2f WM3)).
    assert (SUBw3 : sub_fp [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ3 : aJ_on m3).
    { apply (aJ_wout_on [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 API ART AJ2 MU3 WM3 SUBw3).
      intros x Hx.
      destruct (Z_lt_le_dec x (o + 6)) as [Lx|Lx]; [left; cbn [outside]; split; [lia | split; [lia | exact I]]|].
      destruct (Z_lt_le_dec x (o + 6 + 6)) as [Lx2|Lx2].
      - right. destruct (em_rw_bytes rsegs m3 (o + 6) 6 sb RW3) as (_ & HBo3 & _). destruct HBo3 as (_ & _ & HBf3).
        pose proof (HBf3 (Z.to_nat (x - (o + 6))) ltac:(rewrite Hsb; lia)) as HMr3.
        replace (o + 6 + Z.of_nat (Z.to_nat (x - (o + 6)))) with x in HMr3 by lia.
        destruct (nth_error sb (Z.to_nat (x - (o + 6)))) as [bb|] eqn:EN;
          [ exists bb; exact HMr3 | apply nth_error_None in EN; rewrite Hsb in EN; lia ].
      - left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (FR3 : rw_cells rsegs m3 (SP0 + -128)
                    [CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)); C8 s11; C8 s10; C8 s9; C8 s8;
                     C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ FR2 MU3 WM3).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P1'' : rw_cells rsegs m3 o [CB 6 db]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ RW2 MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3'' : rw_cells rsegs m3 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P3' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4'' : rw_cells rsegs m3 (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P4' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    (* E2 of the glue draft: the prefix munch stays tight (aWL), so no widening here. *)
    (* li a0,-13 ; bltu a0,s0,85810 : not taken (o + 1492 <= 2^64) *)
    step. step. if_false.
    (* the header stores (afront_hdr_on), then the continuation *)
    apply (afront_hdr_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns))
             (repeat (Z_to_bv 8 0) 6) HE FR3 ST3 MU3f WM3f MI3 AJ3 P1'' RW3 P3'' P4'').
    intros y10 y11 y12 mc' KMU KWM KMI KAJ KST KFR KP1 KP2 KHB KHW KP18.
    exact (HK _ y10 y11 y12 _ _ _ _ _ _ _ _ _ _ _ _ w0 mc' HE KFR KST KMU KWM KMI KAJ KP1 KP2 KHB KHW KP18).
  Qed.

  (* aent_ms with aJ_on and HMS_on (the call's region by ae_srw_ms). *)
  Lemma aent_ms_on : forall (t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 : word)
      (mc : word -> option byte) (j : list byte),
    aKont_on -> EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG QK
      (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               (zxb (nth 21 row (Z_to_bv 8 0))) x12 x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g)
               (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21 (Z_to_bv 64 md) (Z_to_bv 64 d) x24 x25 x26 (Z_to_bv 64 ASAN_K)
               w0 (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x855a8) fc None mc (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 x12 x13 x16 x19 x21 x24 x25 x26 w0 t5 t6 mc j HK HE FR ST MU0 WM MI.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof ST as (Rlo & _ & _).
    destruct (AO HE) as (AOo & APo & ART).
    destruct (HEo HE) as (HOm & DsoLO & Dof & _).
    pose proof DsoLO as DsoLOu. unfold ly_dj in DsoLOu.
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof alay_fs as (_ & _ & _ & FSL).
    pose proof (addressable_app m o LEN AOo) as API.
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app m LO 4640 AWIN) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    (* aJ_on in the entry memory m (the Section hypotheses, EE = true) *)
    assert (AJm : aJ_on m).
    { unfold aJ_on. split; [exact HAC|]. split; [exact (fun (P : Z -> Prop) (HP : shadow_rw_on P m) => HP)|]. split; [exact AWIN|]. split; [exact AOo|].
      split; [pose proof FP as FP'; rewrite HE in FP'; exact FP' | exact FPT]. }
    (* li a2,1 ; sd t3,0(sp) ; sd t4,16(sp) *)
    step. step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc1 end.
    (* the join at 0x855e8 (sd a7,8(sp)): s10 = a5, s8 = s, s9 = LEN; a0 and a1 differ by path *)
    assert (K : forall a0v a1v : word,
      evtF rsegs RNG QK
        (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 f) a0v a1v
                 (Z_to_bv 64 1) x13 (Z_to_bv 64 s) a5 x16 (Z_to_bv 64 g) (Z_to_bv 64 0) x19 (Z_to_bv 64 n) x21
                 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5 (Z_to_bv 64 ASAN_K)
                 w0 (Z_to_bv 64 ns) t5 t6)
            F (Z_to_bv 64 0x855e8) fc None mc1 (seg_rom rsegs))).
    { intros a0v a1v.
      (* sd a7,8(sp) *)
      step.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc2 end.
      apply arw_cb3' in FR.
      assert (AJ : aJ_on mc2) by exact (aJ_win_on [(LO, SP0)] m mc2 AJm MU0 WM (ain_sub LO ltac:(lia))).
      pose proof AJ as AJc. destruct AJc as (ACm & SWm & _ & AOm & _ & _).
      assert (HOc : rw_cells rsegs mc2 o [CB (Z.to_nat LEN) junk]).
      { apply (rw_cells_transport rsegs [(LO, SP0)] m mc2 o _ HOm MU0 WM).
        cbn [disjoint_from cells_size csize]. lia. }
      assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
      assert (Eo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
      assert (ELEN : bv_unsigned (Z_to_bv 64 LEN) = LEN) by (apply unsigned_lit; lia).
      (* route (C): the memset call's shadow region, from aJ_on's transport and HSW_on *)
      assert (SWms : shadow_rw_on (asan_memset_shadow_R (Z_to_bv 64 o) (Z_to_bv 64 LEN)) mc2)
        by (exact (ae_srw_ms mc2 _ _ Eo ELEN HE SWm)).
      (* mv a0,s0 ; li a1,0 ; mv a2,s9 ; jal checked_memset *)
      do 4 step.
      pose proof HMS_on as HMm.
      unfold asan_memset_contract_F_on, ASAN_MEMSET_K,
        rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMm.
      cbv zeta in HMm.
      (* the footprint premises of asan_memset_contract_F_on for this call (pure [exact] in the search below) *)
      assert (FpWms : rng RNG (SP0 + -128 - 2208) 2208) by (eapply rng_sub; [exact FpWIN | lia | lia]).
      assert (FpIMGms : rng RNG IMG_LO (IMG_HI - IMG_LO))
        by (eapply rng_sub; [exact FpIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia]).
      assert (FpCVwms : rng RNG (shadow_addr (SP0 + -128 - 2208) / 8 * 8)
                          (shadow_addr (SP0 + -128 - 2208 + 2208 - 1) / 8 * 8 + 8
                           - shadow_addr (SP0 + -128 - 2208) / 8 * 8))
        by (unfold shadow_addr;
            exact (FpWSH (SP0 + -128 - 2208) (SP0 + -128 - 2208 + 2208 - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
      assert (FpCVms : rng RNG (shadow_addr o / 8 * 8)
                         (shadow_addr (o + LEN - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8))
        by (unfold shadow_addr; exact (FpSoK HE o (o + LEN - 1) ltac:(lia) ltac:(lia) ltac:(lia))).
      eapply evtF_cut.
      { eapply HMm with (junk := junk) (lo := LO); rewrite ?Esp, ?Eo, ?ELEN;
        first
          [ exact HOc | exact AOm | exact ART | exact ST | exact HHM | exact ACm | exact SWms | exact MI
          | right; exact APo
          | right; apply API; lia
          | destruct DsoLOu as [D1|D1]; solve [ left; lia | right; lia ]
          | (* footprint: pre-asserted below, so the search runs no lia *)
            exact FpRB | exact FpIMGms | exact FpWms | exact (FpO HE)
          | right; exact FpCVms | right; exact FpCVwms
          | lia ]. }
      intros ms' (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m1 & -> & MU1 & WM1
                  & MI1 & ST1 & RW1 & AC1 & SW1).
      rewrite Esp, Eo, ELEN in MU1. rewrite Esp in ST1. rewrite Eo, ELEN in RW1.
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
      fixret.
      assert (SUBw1 : sub_fp [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] aWL).
      { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
      assert (MU : munch aWL m m1).
      { apply (munch_trans _ m mc2 m1).
        - apply em_munch_add; exact MU0.
        - apply (munch_weaken [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)]); [|exact MU1].
          intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
      assert (AJ1 : aJ_on m1).
      { apply (aJ_wout_on [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc2 m1 API ART AJ MU1 WM1 SUBw1).
        intros x Hx.
        destruct (Z_lt_le_dec x o) as [Lx|Lx].
        - left. cbn [outside]. split; [lia | split; [lia | exact I]].
        - destruct (Z_lt_le_dec x (o + LEN)) as [Lx2|Lx2].
          + right. destruct (em_rw_bytes rsegs m1 o (Z.to_nat LEN) (repeat (Z_to_bv 8 0) (Z.to_nat LEN)) RW1)
              as (_ & HBo & _).
            destruct HBo as (_ & _ & HBf).
            pose proof (HBf (Z.to_nat (x - o)) ltac:(rewrite repeat_length; lia)) as HMr.
            replace (o + Z.of_nat (Z.to_nat (x - o))) with x in HMr by lia.
            destruct (nth_error (repeat (Z_to_bv 8 0) (Z.to_nat LEN)) (Z.to_nat (x - o))) as [bb|] eqn:EN.
            * exists bb. exact HMr.
            * apply nth_error_None in EN. rewrite repeat_length in EN. lia.
          + left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (FR1 : rw_cells rsegs m1 (SP0 + -128)
                      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
                       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
                       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra])).
      { apply (rw_cells_transport rsegs [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc2 m1 _ _ FR MU1 WM1).
        cbn [disjoint_from cells_size csize Nat.add length]. lia. }
      assert (WMf : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc2 m1 WM WM1)).
      (* the checked loads of row[0] (at f) and row[1] (at f + 1) *)
      assert (MKm : meta_kept m m1).
      { apply (munch_meta aWL m m1 MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
      assert (ADf1 : addressable m1 f 24) by (apply (addressable_kept m m1 f 24 Af MKm)).
      assert (HRm1 : bytes_at rsegs m1 f row).
      { apply (em_obj rsegs m m1 LO SP0 o LEN f row 24 MU HR ltac:(rewrite Hrl; reflexivity));
          [ exact Dsf | exact Dof ]. }
      pose proof (rd_byte rsegs m1 f row 0 HRm1 ltac:(lia)) as RD0.
      replace (f + Z.of_nat 0) with f in RD0 by lia.
      pose proof (rd_byte rsegs m1 f row 1 HRm1 ltac:(lia)) as RD1.
      change (Z.of_nat 1) with 1 in RD1.
      (* srli a0,s1,3 ; add a0,a0,s11 ; lb a0,0(a0) ; bnez a0,8582c: the slow path 0x8582c is blt s2,a0,8560c
         with s2 = 0, taken because f mod 8 = 0 < k; either way the state at 0x8560c is the same *)
      destruct (a_shadow m1 f 24 f 0 ADf1 ltac:(lia) ltac:(lia)) as (k & RK & OK & KR).
      pose proof (FpSf1 f ltac:(lia)) as RSf0.
      step. rewrite ?(unsigned_lit f) by lia. rewrite rc_shr3.
      step. step. clear RK RSf0. steps_until_if.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      lazymatch goal with
      | |- evtF ?segs ?RNG0 ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : evtF segs RNG0 Q (MS R F B fc rv mm ro));
          [ destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ exact G
            | cbv iota; step;
              rewrite (rc_lts_signed 0 (bv_signed k)) by lia;
              replace (0 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; rewrite Hf8 in OK; destruct OK; lia);
              cbv iota; exact G ]
          | ]
      end.
      clear OK KR.
      (* addi a0,s1,1 ; the check of f + 1 (srli a1 ; add a1 ; lb a1 ; lbu s3,0(s1) = row[0] ; bnez a1,85838;
         slow path 0x85838: andi a2,a0,7 ; blt a2,a1,85624) *)
      step.
      chk_go (f + 1) (Z_to_bv 5 12) (a_shadow m1 f 24 (f + 1) 1 ADf1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 1) ltac:(lia)) no_extra.
      (* lbu s2,0(a0) = row[1] *)
      step.
      eapply aent_mc_on;
        [ exact HK | exact HE | exact FR1 | exact ST1 | exact MU | exact WMf | exact MI1 | exact AJ1 | exact RW1 ].
    }
    (* beq a1,a2,855d4 (a1 = LL, a2 = 1) *)
    step.
    pose proof (rc_u8_range row 21) as R21.
    rewrite (rc_u8_eqb row 21 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 1) as [L1|L1]; cbv iota.
    - (* LL = 1, 0x855d4: mv s10,a5 ; mv s8,a4 ; li a1,36 ; mul a0,a0,a1 ; addi s9,a0,52 *)
      assert (L2n : LL <> 2) by (unfold ubat; unfold rc_u8 in L1; lia).
      pose proof (em_E_wok _ _ _ _ HE L2n) as W.
      do 5 step. rewrite (em_len_word n W).
      replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
        by (unfold em_len; rewrite (proj2 (Z.eqb_neq (ubat row 21) 2) L2n); reflexivity).
      apply K.
    - (* li a0,2 ; bne a1,a0,855d0 *)
      step. step. rewrite (rc_u8_eqb row 21 2) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbn [negb]; cbv iota.
      + (* LL = 2: mv s10,a5 ; mv s8,a4 ; li s9,1492 ; j 855e8 *)
        do 4 step.
        replace (Z_to_bv 64 1492) with (Z_to_bv 64 LEN)
          by (unfold em_len; rewrite (proj2 (Z.eqb_eq (ubat row 21) 2) L2); reflexivity).
        apply K.
      + (* LL = 0, 0x855d0: mv a0,s4 ; then as LL = 1 *)
        assert (L2n : LL <> 2) by exact L2.
        pose proof (em_E_wok _ _ _ _ HE L2n) as W.
        do 6 step. rewrite (em_len_word n W).
        replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
          by (unfold em_len; rewrite (proj2 (Z.eqb_neq (ubat row 21) 2) L2n); reflexivity).
        apply K.
  Qed.

  (* aentry_k with aJ_on (stretch 1 of the glue). *)
  Lemma aentry_k_on :
    (forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word) (mc : word -> option byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128)
      (CB 24 (le8 w0 ++ le8 (Z_to_bv 64 g) ++ le8 (Z_to_bv 64 ns)) ::
       C8 s11 :: C8 s10 :: C8 s9 :: C8 s8 :: C8 s7 :: C8 s6 :: C8 s5 :: C8 s4 :: C8 s3 ::
       C8 s2 :: C8 s1 :: C8 s0 :: [C8 ra]) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    bytes_at rsegs mc (o + 12) HDR -> wr_at rsegs mc (o + 12) (Z.of_nat 6) ->
    rw_cells rsegs mc (o + 18) [CB (Z.to_nat (LEN - 18)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 18)))] ->
    evtF rsegs RNG QK
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f) y10 y11 y12 x13 x14 x15
               x16 x17 (zxb (nth 1 row (Z_to_bv 8 0))) (zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n)
               (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 LEN) a5
               (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8571c) fc None mc (seg_rom rsegs))) ->
    forall (t0 t1 t2 t3 t5 t6 : word),
    evtF rsegs RNG QK
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x853c4) fc None m (seg_rom rsegs)).
  Proof.
    intros HK t0 t1 t2 t3 t5 t6.
    (* the prologue's stores write m itself: keep closed copies of the Section facts used after them *)
    pose proof aent_g1_on as G1. pose proof aent_ms_on as KMS0. pose proof atr_on as ATR. pose proof a_shadow as ASH.
    pose proof (ain_sub (bv_unsigned sp - 4640) ltac:(lia)) as AIN.
    pose proof arng_sp as Rsp.
    pose proof Af as (Hfa & _ & HfE & _). unfold APPMEM_END in HfE.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp - 4640, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp - 4640, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. unfold HIGHMEM_BEG in HHM.
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    (* addi sp,sp,-128 ; the 13 saves *)
    step. carve_frame 128%nat ST. do 13 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    (* beqz a1,85810 : not taken (f <> 0) *)
    step. rewrite rc_eqb by lia. replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf0). cbv iota.
    (* mv s1,a1 ; andi s2,a1,7 ; bnez s2,85810 : not taken (f mod 8 = 0) *)
    step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 f)) 7) with 0
      by (rewrite unsigned_lit by lia; rewrite rc_land7; symmetry; exact Hf8).
    step. if_false.
    (* mv s4,a6 ; mv s7,a3 ; mv s6,a2 ; mv s0,a0 ; auipc ; ld (GOT) ; ld s11 (ASAN_K) *)
    do 7 step.
    clear RG RC.
    (* addi a0,s1,21 ; the instrumented check of the byte f + 21 *)
    step.
    pose proof (ATR _ m1 MU WM AIN) as (AC1 & SW1 & FP1 & ADT1).
    pose proof (ADT1 _ _ Af) as ADf1.
    chk_go (f + 21) (Z_to_bv 5 12) (ASH m1 f 24 (f + 21) 21 ADf1 ltac:(lia) ltac:(lia)) (FpSf1 (f + 21) ltac:(lia)) no_extra.
    eapply G1; [exact KMS0 | exact HK | eassumption ..].
  Qed.

End Emit.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The asan-ubsan footprint form of ctrl_emit_as (image B): the run as an ExecF.evtF under a footprint RNG, from the
   callee footprint forms. The Section's rng hypotheses are the consequences of ctrl_emit_as_contract_F's premises;
   the shadow ones go through shcov_byte / shcov_sub with ASAN_K the shadow offset the run reads from the runtime
   cell. ctrl_emit_as_contract_of_F (lib/B/Prog/ctrl_emit_as_c.v) turns this back into the old ctrl_emit_as_contract. *)
Theorem ctrl_emit_as_holds_F :
  asan_memset_contract_F -> asan_memcpy_contract_F -> ctrl_lay_block_contract_F -> reac_braid_encode_ns0_contract_F ->
  ctrl_finish_contract_F -> ctrl_emit_as_contract_F.
Proof.
  intros HMS HMC HLB HBR HFN. unfold ctrl_emit_as_contract_F, CTRL_EMIT_AS, CTRL_EMIT_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  cbv zeta.
  intros -> -> -> -> -> -> -> ->.
  intros Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR Hk Hc HL HG HA Hao Htm Hc2 HLA
    Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  intros RcRB RcWIN RcWSH RcFS RcFSH RcIMG RcTLS RcROW RcROWS RcMD RcMDS RcD RcDS RcS RcSS RcO RcTM RcNB RcG RcJ14
    RcJ13.
  pose proof RcRB as FpRB.
  (* the window data/shadow and side-stack data/shadow *)
  pose proof RcWIN as FpWIN.
  assert (FpWSH : forall a b, bv_unsigned sp - 4640 <= a -> a <= b -> b <= bv_unsigned sp - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG (bv_unsigned sp - 4640) 4640 a b RcWSH H1 H2 ltac:(lia))).
  pose proof RcFS as FpFS.
  assert (FpFSH : forall a b, FS <= a -> a <= b -> b <= FS + FS_SIZE - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG FS FS_SIZE a b RcFSH H1 H2 H3)).
  pose proof RcIMG as FpIMG.
  (* the GOT cell and the runtime cell are in the image *)
  assert (FpGOT : rng RNG GOT_CELL_K 8)
    by (eapply rng_sub; [exact RcIMG | unfold GOT_CELL_K | unfold GOT_CELL_K]; lia).
  assert (FpCELL : rng RNG CELL_K 8)
    by (eapply rng_sub; [exact RcIMG | unfold CELL_K | unfold CELL_K]; lia).
  pose proof RcTLS as FpTLS.
  (* row *)
  pose proof RcROW as FpROW.
  assert (FpSf1 : forall x, f <= x <= f + 23 -> rng RNG (x / 8 + ASAN_K) 1)
    by (intros x Hx; exact (shcov_byte RNG f 24 x RcROWS ltac:(lia))).
  assert (FpSfK : forall a b, f <= a -> a <= b -> b <= f + 23 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG f 24 a b RcROWS H1 H2 ltac:(lia))).
  (* md *)
  pose proof RcMD as FpMD.
  assert (FpSmd1 : forall x, md <= x <= md + 295 -> rng RNG (x / 8 + ASAN_K) 1)
    by (intros x Hx; exact (shcov_byte RNG md 296 x RcMDS ltac:(lia))).
  assert (FpSmdK : forall a b, md <= a -> a <= b -> b <= md + 295 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG md 296 a b RcMDS H1 H2 ltac:(lia))).
  (* d, s *)
  pose proof RcD as FpD.
  assert (FpSdK : forall a b, d <= a -> a <= b -> b <= d + 5 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG d 6 a b RcDS H1 H2 ltac:(lia))).
  pose proof RcS as FpS.
  assert (FpSsK : forall a b, s <= a -> a <= b -> b <= s + 5 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros a b H1 H2 H3; exact (shcov_sub RNG s 6 a b RcSS H1 H2 ltac:(lia))).
  (* output (guarded by EE) *)
  assert (FpO : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true -> rng RNG o (em_len (ubat row 21) n))
    by (intros HE; exact (proj1 (RcO HE))).
  assert (FpSo1 : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true ->
    forall x, o <= x <= o + em_len (ubat row 21) n - 1 -> rng RNG (x / 8 + ASAN_K) 1)
    by (intros HE x Hx; exact (shcov_byte RNG o (em_len (ubat row 21) n) x (proj2 (RcO HE)) ltac:(lia))).
  assert (FpSoK : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true ->
    forall a b, o <= a -> a <= b -> b <= o + em_len (ubat row 21) n - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros HE a b H1 H2 H3; exact (shcov_sub RNG o (em_len (ubat row 21) n) a b (proj2 (RcO HE)) H1 H2 ltac:(lia))).
  (* tm (guarded k=2) *)
  assert (FpTM : ly_k row = 2 -> rng RNG (ly_tm row) 32) by (intros Hk2; exact (proj1 (RcTM Hk2))).
  assert (FpTMK : ly_k row = 2 -> forall a b, ly_tm row <= a -> a <= b -> b <= ly_tm row + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros Hk2 a b H1 H2 H3; exact (shcov_sub RNG (ly_tm row) 32 a b (proj2 (RcTM Hk2)) H1 H2 ltac:(lia))).
  (* name (guarded nm) *)
  assert (FpNB : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\ rname mb <> 0 ->
    rng RNG (rname mb) (Z.of_nat (length nb))) by (intros HNM; exact (proj1 (RcNB HNM))).
  assert (FpNBK : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\ rname mb <> 0 ->
    forall a b, rname mb <= a -> a <= b -> b <= rname mb + Z.of_nat (length nb) - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros HNM a b H1 H2 H3; exact (shcov_sub RNG (rname mb) (Z.of_nat (length nb)) a b (proj2 (RcNB HNM)) H1 H2 ltac:(lia))).
  (* g (guarded) *)
  assert (FpG : g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row)) by (intros G0 A0; exact (proj1 (RcG G0 A0))).
  assert (FpGK : g <> 0 -> ly_al row <> 0 -> forall a b, g <= a -> a <= b -> b <= g + ly_al row - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros G0 A0 a b H1 H2 H3; exact (shcov_sub RNG g (ly_al row) a b (proj2 (RcG G0 A0)) H1 H2 ltac:(lia))).
  (* JOIN (guarded) *)
  assert (FpJ14 : ly_k row = 5 -> rng RNG JOIN_0014 32)
    by (intros Hk5; eapply rng_sub; [exact RcIMG | unfold JOIN_0014 | unfold JOIN_0014]; lia).
  assert (FpSJ14 : ly_k row = 5 -> forall a b, JOIN_0014 <= a -> a <= b -> b <= JOIN_0014 + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros Hk5 a b H1 H2 H3; exact (shcov_sub RNG JOIN_0014 32 a b (RcJ14 Hk5) H1 H2 ltac:(lia))).
  assert (FpJ13 : ly_k row = 6 -> rng RNG JOIN_0013 32)
    by (intros Hk6; eapply rng_sub; [exact RcIMG | unfold JOIN_0013 | unfold JOIN_0013]; lia).
  assert (FpSJ13 : ly_k row = 6 -> forall a b, JOIN_0013 <= a -> a <= b -> b <= JOIN_0013 + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8))
    by (intros Hk6 a b H1 H2 H3; exact (shcov_sub RNG JOIN_0013 32 a b (RcJ13 Hk6) H1 H2 ltac:(lia))).
  (* QK is a post VARIABLE (E1), so the post no longer pins the byte-list arguments: name them here. *)
  eapply aentry_k with (row := row) (tb := tb) (mb := mb) (nb := nb) (gb := gb) (db := db) (sb := sb)
                       (junk := junk) (FS := FS).
  all: try eassumption.
  (* HQK0: QK is the contract's post, so the lift of the EE = false exits is the identity (E1) *)
  - intros ms_ _ HP_. exact HP_.
  (* HK: the prefix hands the tight munch aWL; alay_call takes the wide list (E2) *)
  - intros x1c y10c y11c y12c x13c x14c x15c x16c x17c u0c u1c u2c u3c u4c u5c u6c w0c mc
      HEc FRc STc MUc WMc MIc AJc P1c P2c PHc HWc P18c.
    eapply alay_call with (row := row) (tb := tb) (mb := mb) (nb := nb) (gb := gb) (db := db) (sb := sb)
                          (junk := junk) (FS := FS); try eassumption.
    (* the one premise eassumption cannot close: alay_call takes the wide munch (E2) *)
    refine (munch_weaken _ _ _ _ _ MUc).
    intros xx Hxx. cbn [outside app] in Hxx |- *.
    destruct Hxx as (Hx1 & Hx2 & _). split; [exact Hx1 | split; [exact Hx2 | exact I]].
Qed.

(* Route (C): the _on names (a Theorem Labs lane), resolved and audited. *)
About OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aentry_k_on.
About OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.alay_ret_on.
Print OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.ctrl_emit_as_stretch_shadow_R.
Print OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aJ_on.
Print OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aQp_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aentry_k_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aentry_k_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.alay_ret_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.alay_ret_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.atr_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.atr_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aepi_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ctrl_emit_asF.aepi_on.
Locate asan_memset_contract_F_on.
Locate asan_memcpy_contract_F_on.
Locate ctrl_finish_contract_F_on.
Locate shadow_rw_on.
Locate ae_fl_shadow_rw_on.
Locate sh_word_on.
