(* The whole-function footprint run of ctrl_emit_as (image A) CUT AT ONE POINT, for the cgif-form glue: the
   call of ctrl_lay_block at 0x84cec.  The run of ctrl_lay_block holds the only fake-stack allocation of this
   run (ctrl_emit_as itself calls no __asan_stack_malloc), so the cut is there and nowhere else:
     - ctrl_emit_as_pre_lay_F: 0x849d8 (the entry) -> the state just before the `jal` at 0x84cec, with the
       registers (a0 = o, a1 = f, a2 = md, a3 = g) and the memory the call receives (aMid, which also carries
       the early return of the EE = false regime, which never reaches the call);
     - ctrl_emit_as_post_lay_F: the return point 0x84cf0, with the post of ctrl_lay_block as a premise on the
       state, -> ret;
     - ctrl_emit_as_holds_F_of_split: the two, plus ctrl_lay_block_contract_F, give back the statement of
       ctrl_emit_asF.v's ctrl_emit_as_holds_F, so the cut loses nothing.
   The scripts are those of ctrl_emit_asF.v (not in this delivery) (which this file does not touch; a Theorem Labs lane owns it): the same run
   over StepF's step, the same per-region rng premises, the same callee contracts, with the one change the cut
   needs (the post of the first stretch is aMid, not aQp) and with __asan_memset and __asan_memcpy taken
   through a Theorem Labs lane's own footprint texts, asan_memset_cF.asan_memset_contract_F and
   asan_memcpy_cF.asan_memcpy_contract_F (applied with named arguments), instead of the canonical-shape copies
   ctrl_emit_asF.v (not in this delivery) states for itself.  reac_braid_encode (0x84d20) and ctrl_finish (0x84d2c) stay inside the
   second stretch as reac_braid_encode_ns0_contract_F and ctrl_finish_contract_F.

   Every access of this image's own code is closed from one rng premise, as in ctrl_emit_asF.v: the 128-byte
   frame and the two frame words at SP0 + -120 and SP0 + -112, inside the window [LO, SP0); the 8-byte loads of
   the GOT cell 0x9fad0 and of the runtime cell 0xa8878 that holds the shadow offset (both inside the image
   range); the 1-byte loads of the row bytes f, f + 1, f + 21, f + 22, f + 23; the 4-byte load of md + 56; the
   six checked 1-byte stores at o + 12 .. o + 17 and the two at o + LEN - 2, o + LEN - 1; and the 1-byte load
   of the shadow byte of each checked byte ((x >> 3) + ASAN_K, inside the 8-aligned shadow-word cover of its
   buffer, ashb).

   PROVENANCE: image root lib/A/Img0.v of this tree, the asan build A of libreac v1.9.0,
   (internal path) (sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd); v1.9 numerals throughout (entry 0x849d8,
   the call 0x84cec, the return point 0x84cf0, the GOT cell 0x9fad0, the shadow-offset cell 0xa8878).
   The instructions at the cut, read from that ELF: 0x84cdc addi a0,s4,0; 0x84ce0 addi a1,s3,0; 0x84ce4
   addi a2,s6,0; 0x84ce8 addi a3,s8,0; 0x84cec jal ra,0x855f4 (ctrl_lay_block); 0x84cf0 addi a0,s3,23. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcFinLib RcEmit RcEmitLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  asan_memcpy_c asan_memset_c ctrl_lay_block_c reac_braid_encode_ns0_c ctrl_finish_c reac_box_model_block_c
  ctrl_emit_as_c ImgBounds.
(* a Theorem Labs lane's footprint texts of the two helpers, kept qualified; rng_asan is their one home for
   sh_word_rng / sh_al8_lo / sh_al8_hi (both _cF files Require Export it). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan asan_memcpy_cF asan_memset_cF.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes StepF.
Local Ltac lia ::= em_lia.
Import ListNotations.
Open Scope Z_scope.

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


(* The shadow address is a division, which lia only sees after Z.div_mod_to_equations.  The Section's own shadow
   premises are quantified over their endpoints (a Theorem Labs lane, 2026-10-27 17:42Z: no ground division bound in a lemma's
   context), so this runs on small goals only. *)
Ltac dlia := first [ lia | (Z.div_mod_to_equations; lia) ].

Local Ltac acc_hint ::=
  first
  [ match goal with
    | H : rng ?RNG _ _ |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
        let nz := eval cbv in (Z.of_nat n) in
        apply (rng_acc_litZ' RNG _ _ E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        split; dlia
    end
  | match goal with
    | H : rng ?RNG _ _ |- acc_in ?RNG (?x, ?n) =>
        let nz := eval cbv in (Z.of_nat n) in
        apply (rng_acc_varZ RNG _ _ x n nz H (@eq_refl Z nz));
        split; (rewrite ?unsigned_lit by lia); dlia
    end ].

(* An 8-aligned shadow-word cover holds the cover of every sub-range (em_shcov_sub) and the single shadow byte of
   every byte it covers (em_shcov_byte). *)
Lemma em_shcov_sub : forall (R : footprint) a b p q,
  rng R (shadow_addr a / 8 * 8) (shadow_addr b / 8 * 8 + 8 - shadow_addr a / 8 * 8) ->
  a <= p -> q <= b ->
  rng R (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof.
  intros R a b p q H Hp Hq.
  pose proof (Z.div_le_mono a p 8 ltac:(lia) Hp) as D1.
  pose proof (Z.div_le_mono q b 8 ltac:(lia) Hq) as D2.
  unfold shadow_addr in *.
  pose proof (Z.div_le_mono (a / 8 + ASAN_K) (p / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_le_mono (q / 8 + ASAN_K) (b / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D4.
  eapply rng_sub; [exact H | lia | lia].
Qed.

(* The byte-exact shadow span of [p, q] inside an 8-aligned cover (the shape ctrl_finish_contract_F names). *)
Lemma em_shspan : forall (R : footprint) a b p q,
  rng R (shadow_addr a / 8 * 8) (shadow_addr b / 8 * 8 + 8 - shadow_addr a / 8 * 8) ->
  a <= p -> q <= b -> rng R (p / 8 + ASAN_K) (q / 8 - p / 8 + 1).
Proof.
  intros R a b p q H Hp Hq. unfold shadow_addr in *.
  pose proof (Z.div_le_mono a p 8 ltac:(lia) Hp) as D1.
  pose proof (Z.div_le_mono q b 8 ltac:(lia) Hq) as D2.
  pose proof (Z.mod_pos_bound (a / 8 + ASAN_K) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (a / 8 + ASAN_K) 8 ltac:(discriminate)) as M2.
  pose proof (Z.mod_pos_bound (b / 8 + ASAN_K) 8 ltac:(lia)) as M3.
  pose proof (Z.div_mod (b / 8 + ASAN_K) 8 ltac:(discriminate)) as M4.
  eapply rng_sub; [exact H | lia | lia].
Qed.

Lemma em_shcov_byte : forall (R : footprint) x,
  rng R (shadow_addr x / 8 * 8) (shadow_addr x / 8 * 8 + 8 - shadow_addr x / 8 * 8) ->
  rng R (x / 8 + ASAN_K) 1.
Proof.
  intros R x H. unfold shadow_addr in *.
  pose proof (Z.mod_pos_bound (x / 8 + ASAN_K) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (x / 8 + ASAN_K) 8 ltac:(discriminate)) as M3.
  eapply rng_sub; [exact H | lia | lia].
Qed.

(* The regions of ctrl_lay_block_contract_F that this run supplies from its own premises: the thread pointer words
   and the thread cells (both in fp_tls, which ctrl_emit_as_rtls covers), and the shadow of the class-0 and class-1
   side-stack frames (inside the shadow cover of the side stack). *)
Lemma tls_rng_of_rtls : forall (R : footprint) m TP, ctrl_emit_as_rtls R m TP -> ctrl_lay_block_tls_rng R m TP.
Proof.
  intros R m TP H DT TS C T DB k HT. specialize (H DT TS C T DB k HT). unfold fp_tls in H.
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

Lemma tp_rng_of_rtls : forall (R : footprint) m TP cs FS lo hi W D, fp cs m TP FS lo hi W D ->
  ctrl_emit_as_rtls R m TP -> rng R (TP - 88) 8 /\ rng R (TP - 8) 24.
Proof.
  intros R m TP cs FS lo hi W D (DT & TS & C & T & DB & k & HT & _) H.
  specialize (H DT TS C T DB k HT). unfold fp_tls in H.
  do 2 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [H8 H].
  do 3 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [H88 _].
  cbn [fst snd] in H8, H88.
  split; [eapply rng_sub; [exact H88 | lia | lia] | eapply rng_sub; [exact H8 | lia | lia]].
Qed.

Lemma fs_frame_shadow_rng : forall (R : footprint) FS c, (c = 0 \/ c = 1)%nat ->
  rng R (shadow_addr FS / 8 * 8) (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
  rng R (shadow_addr (fs_frame FS c 0)) (fs_M c * fs_B c / 8).
Proof.
  intros R FS c Hc H.
  assert (E : fs_M c * fs_B c / 8 = 131072) by (destruct Hc as [-> | ->]; reflexivity).
  assert (Hc' : 0 <= Z.of_nat c <= 1) by (destruct Hc as [-> | ->]; cbn; lia).
  assert (EF : fs_frame FS c 0 = FS + 36864 + Z.of_nat c * 1048576)
    by (unfold fs_frame; change (2 ^ 20) with 1048576; lia).
  rewrite E, EF.
  pose proof (em_shspan R FS (FS + FS_SIZE - 1) (FS + 36864 + Z.of_nat c * 1048576)
                (FS + 36864 + Z.of_nat c * 1048576 + 1048575) H ltac:(lia) ltac:(unfold FS_SIZE; lia)) as Hs.
  unfold shadow_addr in *. set (x := FS + 36864 + Z.of_nat c * 1048576) in *.
  assert (D : (x + 1048575) / 8 = (x + 7) / 8 + 131071).
  { replace (x + 1048575) with (x + 7 + 131071 * 8) by lia. apply Z.div_add. lia. }
  pose proof (Z.div_le_mono x (x + 7) 8 ltac:(lia) ltac:(lia)) as D2.
  eapply rng_sub; [exact Hs | lia | rewrite D; lia].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The footprint forms of the five callees are their owners' texts: __asan_memset and __asan_memcpy take
   a Theorem Labs lane's asan_memset_cF.asan_memset_contract_F and asan_memcpy_cF.asan_memcpy_contract_F (the image
   [IMG_LO, IMG_HI), the munch window, each data range, and the 8-ALIGNED shadow WORD span of each range and of
   the helper's own frame); ctrl_lay_block, reac_braid_encode (ns0) and ctrl_finish take
   ctrl_lay_block_contract_F, reac_braid_encode_ns0_contract_F and ctrl_finish_contract_F of their _c files. *)

Section Emit.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o f md d s g n ns FS : Z) (row tb mb nb gb db sb junk : list byte)
    (RNG : footprint).

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

  Hypothesis HMS : asan_memset_cF.asan_memset_contract_F.
  Hypothesis HMC : asan_memcpy_cF.asan_memcpy_contract_F.
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

  (* The footprint premises of ctrl_emit_as_contract_F.  A shadow cover is quantified over its endpoints
     (a Theorem Labs lane, 2026-10-27 17:42Z: no ground division bound in a lemma's context); each is the contract's one
     ground 8-aligned cover of that buffer by em_shcov_sub. *)
  Hypothesis RRB : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG LO 4640.
  Hypothesis RWSH : forall p q, LO <= p -> q <= SP0 - 1 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RFS : rng RNG FS FS_SIZE.
  Hypothesis RFSH : forall p q, FS <= p -> q <= FS + FS_SIZE - 1 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RTLS : ctrl_emit_as_rtls RNG m (bv_unsigned tp).
  Hypothesis RROW : rng RNG f 24.
  Hypothesis RROWS : forall p q, f <= p -> q <= f + 23 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RMD : rng RNG md 296.
  Hypothesis RMDS : forall p q, md <= p -> q <= md + 295 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RDB : rng RNG d 6.
  Hypothesis RDBS : forall p q, d <= p -> q <= d + 5 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RSB : rng RNG s 6.
  Hypothesis RSBS : forall p q, s <= p -> q <= s + 5 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RTM : KB = 2 -> rng RNG (ly_tm row) 32.
  Hypothesis RTMS : KB = 2 -> forall p q, ly_tm row <= p -> q <= ly_tm row + 31 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RNB : NM -> rng RNG (rname mb) (Z.of_nat (length nb)).
  Hypothesis RNBS : NM -> forall p q, rname mb <= p -> q <= rname mb + Z.of_nat (length nb) - 1 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RGB : g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row).
  Hypothesis RGBS : g <> 0 -> ly_al row <> 0 -> forall p q, g <= p -> q <= g + ly_al row - 1 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis ROB : EE = true -> rng RNG o LEN.
  Hypothesis ROBS : EE = true -> forall p q, o <= p -> q <= o + LEN - 1 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RJ14S : KB = 5 -> forall p q, JOIN_0014 <= p -> q <= JOIN_0014 + 31 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
  Hypothesis RJ13S : KB = 6 -> forall p q, JOIN_0013 <= p -> q <= JOIN_0013 + 31 ->
    rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).

  (* The shadow byte of every byte this run checks itself: a byte of the row, of md, or of the output. *)
  Lemma ashb : forall x, f <= x < f + 24 \/ md <= x < md + 296 \/ (EE = true /\ o <= x < o + LEN) ->
    rng RNG (x / 8 + ASAN_K) 1.
  Proof.
    intros x [Hx | [Hx | (HE & Hx)]]; apply em_shcov_byte.
    - exact (RROWS x x ltac:(lia) ltac:(lia)).
    - exact (RMDS x x ltac:(lia) ltac:(lia)).
    - exact (ROBS HE x x ltac:(lia) ltac:(lia)).
  Qed.

  Ltac sh_in := first [ left; lia | right; left; lia | right; right; split; [assumption | lia] ].

  (* The runtime cells the prologue reads, from the image range. *)
  Lemma argk : rng RNG GOT_CELL_K 8.
  Proof. eapply rng_sub; [exact RIMG | unfold GOT_CELL_K; lia | unfold GOT_CELL_K; lia]. Qed.
  Lemma arck : rng RNG CELL_K 8.
  Proof. eapply rng_sub; [exact RIMG | unfold CELL_K; lia | unfold CELL_K; lia]. Qed.
  Lemma arrt : rng RNG RT_LO (RT_HI - RT_LO).
  Proof. eapply rng_sub; [exact RIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia]. Qed.

  (* The image range as a Theorem Labs lane's contracts name it (lib/A/Prog/ImgBounds.v): [IMG_LO, IMG_HI) is the range
     RIMG gives, [0x10000, 0x10000 + 0x5ee000). *)
  Lemma aimg : rng RNG IMG_LO (IMG_HI - IMG_LO).
  Proof. eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia]. Qed.

  (* a Theorem Labs lane's 8-aligned shadow WORD span of [pp, pp + nn): rng_asan.sh_word_rng, the one home of the text
     both asan_memcpy_cF.v and asan_memset_cF.v export, from one of this run's 8-aligned covers.  nn > 0 at
     every call of this run, so the nn = 0 guard is never taken. *)
  Lemma acpy_shw : forall aa bb pp nn,
    rng RNG (shadow_addr aa / 8 * 8) (shadow_addr bb / 8 * 8 + 8 - shadow_addr aa / 8 * 8) ->
    aa <= pp -> pp + nn - 1 <= bb -> 0 < nn -> rng_asan.sh_word_rng RNG pp nn.
  Proof.
    intros aa bb pp nn H Hp Hq Hz.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi.
    right. exact (em_shcov_sub RNG aa bb pp (pp + nn - 1) H Hp Hq).
  Qed.

  Lemma aset_shw : forall aa bb pp nn,
    rng RNG (shadow_addr aa / 8 * 8) (shadow_addr bb / 8 * 8 + 8 - shadow_addr aa / 8 * 8) ->
    aa <= pp -> pp + nn - 1 <= bb -> 0 < nn -> rng_asan.sh_word_rng RNG pp nn.
  Proof.
    intros aa bb pp nn H Hp Hq Hz.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi.
    right. exact (em_shcov_sub RNG aa bb pp (pp + nn - 1) H Hp Hq).
  Qed.

  Definition aRES (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0)) BLK LEN)
    /\ (LL <> 2 -> em_wok n = true)
    /\ (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).

  (* The post of a run that ends at ret, with its munch window W counted from a base memory mb.  The whole
     function takes mbz = m and the cumulative window (aQp below, the post of ctrl_emit_as_contract_F); the
     second stretch takes mbz = the memory ctrl_lay_block returns and its OWN window, which holds no
     fp_w [0; 1] FS range because that stretch allocates no fake-stack frame. *)
  Definition aQg (mbz : word -> option byte) (W : list ivl) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch W mbz m'
      /\ wmono rsegs mbz m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ shadow_rw m' /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (EE = true -> aRES m').

  Definition aQp : machine_state -> Prop :=
    aQg m (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]).

  Lemma arng_sp : 4640 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma ain_sub : forall lo', LO <= lo' -> sub_fp [(lo', SP0)] [(LO, SP0)].
  Proof. intros lo' H x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* The bundled runtime state carried across the body (EE = true regime: the output is [o, o + LEN)). *)
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


  (* The thread cells of a memory this run reached: the writes so far are inside aWL, which fp names apart from
     the cells, so the cells keep their bytes and the pointers read from them are those of m (fl_tls_same); the
     rng premises of RTLS are therefore the ones of that memory too. *)
  Lemma a_rtls : forall mc W', EE = true -> munch W' m mc -> sub_fp W' aWL ->
    ctrl_emit_as_rtls RNG mc (bv_unsigned tp).
  Proof.
    intros mc W' HE MU SUB DT TS C T DB k HT.
    pose proof FP as FP0. rewrite HE in FP0.
    destruct FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & _ & _ & _ & _ & _ & _ & _ & DJW & _).
    assert (OUT : Forall (fun d => forall x, fst d <= x < snd d -> outside W' x)
                    (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { pose proof (fl_cols aWL W' _ DJW SUB) as O. apply Forall_app in O. exact (proj1 O). }
    destruct (fl_tls_same m mc W' (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k TLS0 HT MU OUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst.
    exact (RTLS _ _ _ _ _ _ TLS0).
  Qed.

  (* The epilogue (+0x394 .. +0x3d0): the return value RR, the register restores and ret.  It writes nothing,
     so the base memory mbz and the window W are the ones its caller hands in: the whole run takes mb = m with
     the cumulative window, the second stretch takes mbz = the memory ctrl_lay_block returns with its own. *)
  Lemma aepi : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (W : list ivl) (j : list byte) (r : Z),
    r = RR -> 0 <= r < 2^64 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch W mbz mc -> wmono rsegs mbz mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw mc -> addressable mc LO 4640 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD ->
    (EE = true -> aRES mc) ->
    evtF rsegs RNG (aQg mbz W)
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 r) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d6c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc mbz W j r Er Rr FR ST MU WM MI AC SW AW FP' HRES.
    pose proof arng_sp as Rsp.
    pose proof ST as (Rlo & _ & _).
    do 16 step.
    apply evtF_done. unfold aQg.
    do 14 eexists. exists mc. rewrite Er.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP'|].
    exact HRES.
  Qed.

  (* The early return (EE = false): go to the epilogue with RR = 0 and no block written.  This path calls
     nothing, so its window is the real stack window alone: no side-stack range and no shadow range. *)
  Lemma aepi0 : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    EE = false ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG (aQg m [(LO, SP0)])
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 0) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d6c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc j HE FR ST MU WM MI.
    pose proof arng_sp as Rsp.
    destruct (atr _ mc MU WM (ain_sub LO ltac:(lia))) as (AC & SW & FP' & ADT).
    apply (aepi x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
             u3 u4 u5 u6 mc m _ j 0);
      [rewrite HE; reflexivity | lia | exact FR | exact ST | exact MU | exact WM | exact MI
       | exact AC | exact SW | exact (ADT _ _ AWIN) | exact FP' | rewrite HE; intros H; discriminate H].
  Qed.

  (* The shadow-check tactics, as in lib/A/Prog/declaration_of.v. *)
  Ltac steps_to P :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; steps_to P
    end.
  Ltac steps_until_if :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
    | _ => idtac
    end.
  Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.
  Ltac no_extra X := idtac.
  Ltac chk_go X r SH extra :=
    let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
    let RSH := fresh "RSH" in
    pose proof (ashb X ltac:(sh_in)) as RSH;
    destruct SH as (k & RK & OK & KR);
    step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
    step; step; clear RK; steps_until_if;
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

  (* A shadow read of the byte o + j from addressable mc o LEN (as declaration_of's da_shadow). *)
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

  Local Abbreviation HDR :=
    [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
     Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)].

  (* The 13 saved registers of this function's frame, at SP0 + -104. *)
  Local Abbreviation aFT := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0;
                             C8 ra].

  (* ---- The cut of the run at the ctrl_lay_block call (0x84cec).  ctrl_emit_as itself calls no
     __asan_stack_malloc; the only fake-stack allocation of this run happens inside ctrl_lay_block, so the run
     is cut at that one call and nowhere else (reac_braid_encode at 0x84d20 and ctrl_finish at 0x84d2c stay
     inside the second stretch as their _F contracts, __asan_memset and __asan_memcpy inside the first as
     a Theorem Labs lane's asan_memset_cF / asan_memcpy_cF). ----

     aAtLay: the state at the call site, with the registers and the memory the call receives: a0 = o, a1 = f,
     a2 = md, a3 = g (the four addi at 0x84cdc .. 0x84ce8, the state just before the `jal`), this function's
     frame at SP0 + -128 and the output as the checked memset and the two checked memcpy left it.  Every fact
     the premises of ctrl_lay_block_contract_F are built from travels in it; nothing else crosses the cut. *)
  Definition aAtLay : machine_state -> Prop :=
    fun ms' => exists (x1 u0 u1 u2 x8 x9 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                      (mc : word -> option byte) (j0 : list byte) (P : word),
      ms' = MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9
                    (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g) x14 x15 x16 x17
                    (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d)
                    (Z_to_bv 64 g) (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
               F (Z_to_bv 64 0x84cec) fc None mc (seg_rom rsegs)
      /\ EE = true /\ length j0 = 8%nat /\ aJ mc /\ stk rsegs mc LO (SP0 + -128)
      /\ munch aWL m mc /\ wmono rsegs m mc /\ mem_inv rsegs mc
      /\ rw_cells rsegs mc (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT)
      /\ rw_cells rsegs mc o [CB 6 db] /\ rw_cells rsegs mc (o + 6) [CB 6 sb]
      /\ rw_cells rsegs mc (o + 12) [CB 6 HDR]
      /\ rw_cells rsegs mc (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)]
      /\ rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))]
      /\ rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)].

  (* The post of the first stretch: the call site, or the early return (EE = false), which never reaches the
     call and has already returned.  The early-return arm carries the run's OWN window, the real stack window
     [LO, SP0) alone: that path calls nothing, so it writes no side-stack byte and no shadow byte, and a
     journal can cross it.  aQp_of_win0 widens it to the whole function's post. *)
  Definition aMid : machine_state -> Prop :=
    fun ms' => aQg m [(LO, SP0)] ms' \/ aAtLay ms'.

  Lemma amid_q : forall ms', evtF rsegs RNG (aQg m [(LO, SP0)]) ms' -> evtF rsegs RNG aMid ms'.
  Proof.
    intros ms' H. apply (evtF_mono rsegs RNG (aQg m [(LO, SP0)]) aMid ms' H).
    intros x Hx. left. exact Hx.
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

  (* fp for the ctrl_lay_block call: the callee's frame [LO, SP0 + -128) and its block window [o + 18, o + 50)
     lie inside this function's window and output; fl_fp_sub shrinks aJ's fp to it. *)
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

  (* ---- The return-side transport of aJ across the ctrl_lay_block call (0x855f4). This call's write window
     carries fp_w and the stack shadow, so aJ_win / aJ_out / aJ_wout do not apply; aJ_lay is the mirror of
     alay_fp / alay_tls. The callee's post (ctrl_lay_block_c.v) gives asan_cells, shadow_rw, the callee window
     addressable and the returned fp; the output and the saved-register frame [SP0 + -128, SP0) keep their shadow,
     so they transport, and fl_fp_ret / fl_tls_same carry the fp and tls back over [LO, SP0). ---- *)

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

  (* The em_fr trailer (0x84d30 .. 0x84d6c): s4 := o + LEN, then the two checked trailing stores (194 at
     o + LEN - 2, -22 at o + LEN - 1), then the epilogue via aepi. *)
  Lemma atail3 : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25
                        u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL mbz mc ->
    wmono rsegs mbz mc -> mem_inv rsegs mc -> aJ mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 BLK] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)) ->
    evtF rsegs RNG (aQg mbz aWL)
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 o) x21 x22 x23 x24 x25 (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d30) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 u3 u4 u5 u6 mc mbz jf
      HE FR ST MU WM MI AJ P1 P2 P3 P4 P5 P6 CLS.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & Dso & _). unfold ly_dj in Dso.
    destruct (em_rw_bytes rsegs mc (o + LEN + -2) 2 (repeat (Z_to_bv 8 0) 2) P6) as (_ & HB6 & HW6).
    clear P6.
    (* add s4,s4,s10 ; addi a0,s4,-2 *)
    do 2 step.
    chk_go (o + LEN + -2) (Z_to_bv 5 12)
      (a_shadow mc o LEN (o + LEN + -2) (LEN - 2) AOm ltac:(lia) ltac:(lia)) no_extra.
    (* li a0,194 ; sb a0,-2(s4) *)
    assert (HS1 : store_ok rsegs mc (wa (o + LEN + -2)) 1 = true).
    { pose proof (wr_at_store_ok rsegs mc (o + LEN + -2) (Z.of_nat 2) 0 1%nat HW6 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    step. step.
    replace (o + LEN + -2 + Z.of_nat 0) with (o + LEN + -2) by lia.
    rewrite ?em_le1. rewrite (em_byte_lit 194) by lia.
    assert (MU1 : munch aWL mbz
                    (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
      by (apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM1 : wmono rsegs mbz (write_to_mem mc (wa (o + LEN + -2)) [Z_to_bv 8 194]))
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
    (* addi a0,s4,-1 *)
    step.
    chk_go (o + LEN + -1) (Z_to_bv 5 12)
      (a_shadow m1 o LEN (o + LEN + -1) (LEN - 1) AO1 ltac:(lia) ltac:(lia)) no_extra.
    (* li a1,-22 ; sb a1,0(a0) *)
    assert (HS2 : store_ok rsegs m1 (wa (o + LEN + -1)) 1 = true).
    { pose proof (wr_at_store_ok rsegs m1 (o + LEN + -2) (Z.of_nat 2) 1 1%nat HW1 ltac:(lia)
                    ltac:(cbn [Z.of_nat]; lia)) as H. replace (o + LEN + -2 + 1) with (o + LEN + -1) in H by lia.
      exact H. }
    step. step.
    replace (o + LEN + -1 + Z.of_nat 0) with (o + LEN + -1) by lia.
    rewrite ?em_le1. rewrite em_byte_m22.
    assert (MU2 : munch aWL mbz
                    (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
      by (apply munch_write; [exact MU1 | lia | cbn [length]; lia | cbn [inside app length]; right; left; lia]).
    assert (WM2 : wmono rsegs mbz (write_to_mem m1 (wa (o + LEN + -1)) [Z_to_bv 8 234]))
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
    (* transport the output body to m2 *)
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
    - exact MU2.
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

  (* The ctrl_finish call (0x84d24 .. 0x84d30): stamps the block, then the em_fr trailer via atail3. *)
  Lemma atail2 : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25
                        u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL mbz mc ->
    wmono rsegs mbz mc -> mem_inv rsegs mc -> aJ mc ->
    bytes_at rsegs mc f row -> addressable mc (f + 18) 3 ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 LB] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG (aQg mbz aWL)
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 f) (Z_to_bv 64 o) x21 x22 x23 x24 x25 (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K)
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d24) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 u3 u4 u5 u6 mc mbz jf
      HE FR ST MU WM MI AJ HRf ADf3 P1 P2 P3 P4 P5 P6.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
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
      - rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - intros _; rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - exact ACm.
      - exact SWm.
      - exact ADf3.
      - intros _; exact (addressable_sub mc o LEN 18 32 AOm ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros x Hx. rewrite Esp. cbn [outside]. split.
        + unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
            CTRL_FINISH_FRAME in Hx, FSlo |- *; unfold HIGHMEM_BEG in HHM.
          destruct Hx as [HGt|[HCt|HSt]]; lia.
        + apply (em_fin_sub CC RO RL o Hc Hrn Hc2). cbn [outside]. split; [|exact I].
          destruct Hx as [HGt|[HCt|HSt]].
          * unfold GOT_CELL_K in HGt; unfold RT_LO, RT_HI in ART; lia.
          * unfold CELL_K in HCt; unfold RT_LO, RT_HI in ART; lia.
          * pose proof (app_ivl_meta o (o + LEN) x API HSt) as Hm2; lia.
      - rewrite Esp. eapply rng_sub; [exact RWIN | unfold CTRL_FINISH_FRAME; lia | unfold CTRL_FINISH_FRAME; lia].
      - exact argk.
      - exact arck.
      - exact RROW.
      - exact (em_shspan RNG f (f + 23) (f + 18) (f + 20) (RROWS f (f + 23) ltac:(lia) ltac:(lia))
                 ltac:(lia) ltac:(lia)).
      - intros _. split.
        + eapply rng_sub; [exact ROo | lia | lia].
        + exact (em_shspan RNG o (o + LEN - 1) (o + 18) (o + 49)
                   (ROBS HE o (o + LEN - 1) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)). }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & -> & MU1 & WM1 & MI1 & ST1 & HF).
    fixret. rewrite Esp in MU1, ST1.
    pose proof (MI1 MI) as MIm1.
    assert (SUBw : sub_fp ((SP0 + -128 - 16, SP0 + -128) :: fin_w CC RO RL o) aWL).
    { intros x Hx. apply (em_fin_sub2 CC RO RL o (SP0 + -128 - 16, SP0 + -128) Hc Hrn Hc2).
      cbn [outside] in Hx |- *. destruct Hx as (HAx & HBx & _). split; [lia | split; [lia | exact I]]. }
    assert (MU1' : munch [(SP0 + -128 - 16, SP0 + -128); (o + 18, o + 50)] mc m1)
      by (apply (munch_weaken _ _ mc m1 (em_fin_sub2 CC RO RL o (SP0 + -128 - 16, SP0 + -128) Hc Hrn Hc2)); exact MU1).
    assert (MUf : munch aWL mbz m1).
    { apply (munch_trans _ mbz mc m1 MU).
      apply (munch_weaken ((SP0 + -128 - 16, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
      intros x Hx. apply SUBw. cbn [outside app] in Hx |- *. tauto. }
    assert (WMf : wmono rsegs mbz m1) by (exact (wmono_trans rsegs mbz mc m1 WM WM1)).
    assert (AJm1 : aJ m1).
    { apply (aJ_wout ((SP0 + -128 - 16, SP0 + -128) :: fin_w CC RO RL o) mc m1 API ART AJ MU1 WM1 SUBw).
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
        assert (MUw : munch [(SP0 + -128 - 16, SP0 + -128)] mc m1).
        { apply (munch_weaken ((SP0 + -128 - 16, SP0 + -128) :: fin_w CC RO RL o)); [|exact MU1].
          rewrite C0. cbn [fin_w]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
        apply (rw_cells_transport rsegs [(SP0 + -128 - 16, SP0 + -128)] mc m1 _ _ P4 MUw WM1);
          cbn [disjoint_from cells_size csize]; lia.
      - destruct (HF ltac:(lia)) as (HB4 & _ & _). exact HB4. }
    assert (CLS' : CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)).
    { intros HCC. destruct (HF HCC) as (_ & CL1 & CL2). split; [exact CL1 | exact CL2]. }
    eapply (atail3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mbz jf);
      [ exact HE | exact FRm1 | exact ST1 | exact MUf | exact WMf | exact MIm1 | exact AJm1
      | exact P1' | exact P2' | exact P3' | exact P4' | exact P5' | exact P6' | exact CLS' ].
  Qed.

  (* atail_pre: the body 0x84be4 -> 0x84c40 (checked_memset; the row[0]/row[1] loads; the two checked_memcpy),
     ending at the first checked header byte store, handed to the continuation K (atail_k, for atail below). *)
  Lemma atail_pre : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                          (mc : word -> option byte) (jf : list byte)
      (K : forall (y1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (m2 : word -> option byte),
        aJ m2 ->
        stk rsegs m2 LO (SP0 + -128) ->
        munch aWL m m2 ->
        wmono rsegs m m2 -> mem_inv rsegs m2 ->
        rw_cells rsegs m2 (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                                       C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        bytes_at rsegs m2 f row -> addressable m2 f 24 ->
        rw_cells rsegs m2 o [CB 6 db] ->
        rw_cells rsegs m2 (o + 6) [CB 6 sb] ->
        rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells rsegs m2 (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
        rw_cells rsegs m2 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
        rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
        evtF rsegs RNG aMid
          (MS (mkR y1 (Z_to_bv 64 (SP0 + -128)) gp tp w0 w1 w2 (zxb (nth 1 row (Z_to_bv 8 0)))
                   (zxb (nth 0 row (Z_to_bv 8 0))) b0 b1 b2 b3 b4 b5 b6 b7
                   (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
                   (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) w3 w4 w5 w6)
              F (Z_to_bv 64 0x84c40) fc None m2 (seg_rom rsegs))),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                                    C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
               (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x84be4) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc jf K
      HE FR ST MU0 WM MI AJ.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (AOo & APo & ART).
    destruct (HEo HE) as (HOm & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    unfold ly_dj in DsoLO.
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (Eo : bv_unsigned (Z_to_bv 64 o) = o) by (apply unsigned_lit; lia).
    assert (ELEN : bv_unsigned (Z_to_bv 64 LEN) = LEN) by (apply unsigned_lit; lia).
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    assert (HOc : rw_cells rsegs mc o [CB (Z.to_nat LEN) junk]).
    { apply (rw_cells_transport rsegs [(LO, SP0)] m mc o _ HOm MU0 WM).
      cbn [disjoint_from cells_size csize]. lia. }
    (* checked_memset(o, 0, LEN) *)
    do 4 step.
    pose proof HMS as HMm. unfold asan_memset_cF.asan_memset_contract_F, ASAN_MEMSET_K in HMm.
    cbv zeta in HMm.
    eapply evtF_cut.
    { eapply HMm with (RNG := RNG) (junk := junk) (lo := LO); rewrite ?Esp, ?Eo, ?ELEN;
      first
        [ exact HOc | exact AOm | exact ART | exact ST | exact HHM | exact ACm | exact SWm | exact MI
        | exact RRB | exact aimg
        | right; exact APo
        | right; apply API; lia
        | destruct DsoLO as [D1|D1]; solve [ left; lia | right; lia ]
        | lia
        | eapply rng_sub; [exact RWIN | unfold CTRL_EMIT_AS_K; lia | unfold CTRL_EMIT_AS_K; lia]
        | eapply rng_sub; [exact ROo | lia | lia]
        | eapply aset_shw; [exact (ROBS HE o (o + LEN - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia]
        | eapply aset_shw; [exact (RWSH LO (SP0 - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia] ]. }
    intros ms' (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & RW1 & AC1 & SW1).
    rewrite Esp, Eo, ELEN in MU1. rewrite Esp in ST1. rewrite Eo, ELEN in RW1.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
    fixret.
    assert (SUBw1 : sub_fp [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (MU : munch aWL m m1).
    { apply (munch_trans _ m mc m1).
      - apply em_munch_add; exact MU0.
      - apply (munch_weaken [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)]); [|exact MU1].
        intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ1 : aJ m1).
    { apply (aJ_wout [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc m1 API ART AJ MU1 WM1 SUBw1).
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
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc m1 _ _ FR MU1 WM1).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (WMf : wmono rsegs m m1) by (exact (wmono_trans rsegs m mc m1 WM WM1)).
    (* the shadow checks and loads of row[0] (at f) and row[1] (at f + 1) *)
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
    pose proof Af as Afl. destruct Afl as (Hfge & Hfle & _ & _).
    chk_go f (Z_to_bv 5 11) (a_shadow m1 f 24 f 0 ADf1 ltac:(lia) ltac:(lia)) no_extra.
    step.
    chk_go (f + 1) (Z_to_bv 5 12) (a_shadow m1 f 24 (f + 1) 1 ADf1 ltac:(lia) ltac:(lia)) no_extra.
    step.
    (* split the zeroed output; local copies of the facts the two checked_memcpy need *)
    destruct (em_split_frame rsegs m1 o LEN (Z_to_bv 8 0) RW1 ltac:(lia)) as (P1z & P2z & P3z & P4z & P5z & P6z).
    pose proof (bytes_at_bound rsegs m d db HD) as BDb. rewrite Hdb in BDb. change (Z.of_nat 6) with 6 in BDb.
    pose proof (bytes_at_bound rsegs m s sb HSb) as BSb. rewrite Hsb in BSb. change (Z.of_nat 6) with 6 in BSb.
    pose proof APD as APDl. pose proof APS as APSl. pose proof HAE as HAEl.
    pose proof Dsd as Dsdl. unfold ly_dj in Dsdl.
    pose proof Dss as Dssl. unfold ly_dj in Dssl.
    pose proof Dod as Dodl. unfold ly_dj in Dodl.
    pose proof Dos as Dosl. unfold ly_dj in Dosl.
    assert (Ed : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by (apply unsigned_lit; lia).
    pose proof AJ1 as AJ1c. destruct AJ1c as (AC1x & SW1x & AW1x & AO1 & FP1 & TL1).
    assert (ADd1 : addressable m1 d 6) by (apply (addressable_kept m m1 d 6 Ad MKm)).
    assert (ADo1 : addressable m1 o 6) by (apply (addressable_prefix m1 o LEN 6 AO1); lia).
    assert (HDc1 : bytes_at rsegs m1 d db).
    { apply (em_obj rsegs m m1 LO SP0 o LEN d db 6 MU HD ltac:(rewrite Hdb; reflexivity));
        [ exact Dsd | exact Dod ]. }
    (* checked_memcpy(o, d, 6) *)
    do 4 step.
    pose proof HMC as HMc1. unfold asan_memcpy_cF.asan_memcpy_contract_F, ASAN_MEMCPY_K in HMc1.
    cbv zeta in HMc1.
    eapply evtF_cut.
    { eapply HMc1 with (RNG := RNG) (src := db) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO);
      rewrite ?Esp, ?Eo, ?Ed, ?E6;
      [ exact HDc1
      | rewrite Hdb; reflexivity
      | exact P1z
      | lia
      | lia
      | exact ADd1
      | exact ADo1
      | right; exact (proj1 APDl)
      | right; apply API; lia
      | right; split; [ exact (proj2 APDl) | apply API; lia ]
      | lia
      | lia
      | lia
      | exact ST1
      | lia
      | exact HHM
      | lia
      | exact AC1
      | exact SW1
      | exact MI1
      | exact RRB
      | exact aimg
      | eapply rng_sub; [exact RWIN | lia | lia]
      | eapply rng_sub; [exact ROo | lia | lia]
      | exact RDB
      | eapply acpy_shw; [exact (ROBS HE o (o + LEN - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia]
      | eapply acpy_shw; [exact (RDBS d (d + 5) ltac:(lia) ltac:(lia)) | lia | lia | lia]
      | eapply acpy_shw; [exact (RWSH LO (SP0 - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia] ]. }
    intros ms2 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SW2).
    rewrite Esp, Eo, E6 in MU2. rewrite Esp in ST2. rewrite Eo, E6 in RW2.
    change (Z.to_nat 6) with 6%nat in RW2, MU2.
    fixret.
    assert (MU2f : munch aWL m m2).
    { apply (munch_trans _ m m1 m2 MU).
      apply (munch_weaken [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)]); [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (WM2f : wmono rsegs m m2) by (exact (wmono_trans rsegs m m1 m2 WMf WM2)).
    assert (SUBw2 : sub_fp [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] aWL).
    { intros x Hx. cbn [outside] in Hx |- *. split; [lia | split; [lia | exact I]]. }
    assert (AJ2 : aJ m2).
    { apply (aJ_wout [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 API ART AJ1 MU2 WM2 SUBw2).
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
    assert (ADf2 : addressable m2 f 24) by (apply (addressable_kept m m2 f 24 Af MKm2)).
    assert (HRm2 : bytes_at rsegs m2 f row).
    { apply (em_obj rsegs m m2 LO SP0 o LEN f row 24 MU2f HR ltac:(rewrite Hrl; reflexivity));
        [ exact Dsf | exact Dof ]. }
    assert (FR2 : rw_cells rsegs m2 (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ FR1 MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P2' : rw_cells rsegs m2 (o + 6) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ P2z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3' : rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ P3z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4' : rw_cells rsegs m2 (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ P4z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P5' : rw_cells rsegs m2 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ P5z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P6' : rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)]).
    { apply (rw_cells_transport rsegs [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 _ _ P6z MU2 WM2).
      cbn [disjoint_from cells_size csize]. lia. }
    (* checked_memcpy(o + 6, s, 6) *)
    pose proof AJ2 as AJ2c. destruct AJ2c as (AC2x & SW2x & AW2x & AO2 & FP2x & TL2x).
    assert (Es : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (Eo6 : bv_unsigned (Z_to_bv 64 (o + 6)) = o + 6) by (apply unsigned_lit; lia).
    assert (ADs2 : addressable m2 s 6) by (apply (addressable_kept m m2 s 6 As MKm2)).
    assert (ADo6 : addressable m2 (o + 6) 6) by (apply (addressable_sub m2 o LEN 6 6 AO2); lia).
    assert (HSc2 : bytes_at rsegs m2 s sb).
    { apply (em_obj rsegs m m2 LO SP0 o LEN s sb 6 MU2f HSb ltac:(rewrite Hsb; reflexivity));
        [ exact Dss | exact Dos ]. }
    do 4 step.
    pose proof HMC as HMc2. unfold asan_memcpy_cF.asan_memcpy_contract_F, ASAN_MEMCPY_K in HMc2.
    cbv zeta in HMc2.
    eapply evtF_cut.
    { eapply HMc2 with (RNG := RNG) (src := sb) (junk := repeat (Z_to_bv 8 0) 6) (lo := LO);
      rewrite ?Esp, ?Eo6, ?Es, ?E6;
      [ exact HSc2
      | rewrite Hsb; reflexivity
      | exact P2'
      | lia
      | lia
      | exact ADs2
      | exact ADo6
      | right; exact (proj1 APSl)
      | right; apply API; lia
      | right; split; [ exact (proj2 APSl) | apply API; lia ]
      | lia
      | lia
      | lia
      | exact ST2
      | lia
      | exact HHM
      | lia
      | exact AC2
      | exact SW2
      | exact MI2
      | exact RRB
      | exact aimg
      | eapply rng_sub; [exact RWIN | lia | lia]
      | eapply rng_sub; [exact ROo | lia | lia]
      | exact RSB
      | eapply acpy_shw; [exact (ROBS HE o (o + LEN - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia]
      | eapply acpy_shw; [exact (RSBS s (s + 5) ltac:(lia) ltac:(lia)) | lia | lia | lia]
      | eapply acpy_shw; [exact (RWSH LO (SP0 - 1) ltac:(lia) ltac:(lia)) | lia | lia | lia] ]. }
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
    assert (MKm3 : meta_kept m m3).
    { apply (munch_meta aWL m m3 MU3f). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (ADf3 : addressable m3 f 24) by (apply (addressable_kept m m3 f 24 Af MKm3)).
    assert (HRm3 : bytes_at rsegs m3 f row).
    { apply (em_obj rsegs m m3 LO SP0 o LEN f row 24 MU3f HR ltac:(rewrite Hrl; reflexivity));
        [ exact Dsf | exact Dof ]. }
    assert (FR3 : rw_cells rsegs m3 (SP0 + -128)
                    [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                     C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ FR2 MU3 WM3).
      cbn [disjoint_from cells_size csize Nat.add length]. lia. }
    assert (P1'' : rw_cells rsegs m3 o [CB 6 db]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ RW2 MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P3'' : rw_cells rsegs m3 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P3' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P4'' : rw_cells rsegs m3 (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P4' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P5'' : rw_cells rsegs m3 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P5' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    assert (P6'' : rw_cells rsegs m3 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)]).
    { apply (rw_cells_transport rsegs [(o + 6, o + 6 + 6); (SP0 + -128 - 2224, SP0 + -128)] m2 m3 _ _ P6' MU3 WM3).
      cbn [disjoint_from cells_size csize]. lia. }
    apply K; [ exact AJ3 | exact ST3 | exact MU3f | exact WM3f | exact MI3 | exact FR3 | exact HRm3 | exact ADf3
             | exact P1'' | exact RW3 | exact P3'' | exact P4'' | exact P5'' | exact P6'' ].
  Qed.

  (* ---- atail: the body 0x84be4 -> aMid. atail_pre runs 0x84be4 -> 0x84c40; atail_k proves its continuation:
     the six checked header byte stores (0x84c40 .. 0x84cdc), then alay_pre: the four argument moves of the
     ctrl_lay_block call.  The frame at SP0 + -128 holds P at +8 and ns at +16 (stored before 0x84be4); the
     reac_braid_encode call (in the second stretch) loads its a2 and a4 from there. ---- *)

  Lemma afr_merge : forall mc A j0 (a b : word) cs, rw_cells rsegs mc A (CB 8 j0 :: C8 a :: C8 b :: cs) ->
    rw_cells rsegs mc A (CB 24 (j0 ++ le8 a ++ le8 b) :: cs).
  Proof.
    intros mc A j0 a b cs H. pose proof (rw_cells_merge rsegs mc A [] [CB 8 j0; C8 a; C8 b] cs H) as M.
    cbn [app cells_size cells_bytes cbytes csize Nat.add] in M. rewrite app_nil_r in M. exact M.
  Qed.

  Lemma afr_split : forall mc A j0 (a b : word) cs, length j0 = 8%nat ->
    rw_cells rsegs mc A (CB 24 (j0 ++ le8 a ++ le8 b) :: cs) -> rw_cells rsegs mc A (CB 8 j0 :: C8 a :: C8 b :: cs).
  Proof.
    intros mc A j0 a b cs Hl [[Hwf HB] HW]. split; [split|].
    - cbn [cells_wf cell_wf] in *. destruct Hwf as [_ Hwf].
      split; [exact Hl | split; [exact I | split; [exact I | exact Hwf]]].
    - cbn [cells_bytes cbytes] in *. rewrite <- !app_assoc in HB. exact HB.
    - exact HW.
  Qed.

  Lemma a6c : forall mc A (z : byte), rw_cells rsegs mc A [CB 6 (repeat z 6)] ->
    rw_cells rsegs mc A [C1 z; C1 z; C1 z; C1 z; C1 z; C1 z].
  Proof.
    intros mc A z [[_ HB] HW]. split; [split|].
    - exact (conj I (conj I (conj I (conj I (conj I (conj I I)))))).
    - exact HB.
    - exact HW.
  Qed.

  (* rw_cells kept by a run whose writes W leave every byte of the cells. *)
  Lemma a_rwtr : forall W m1 m2 A cs, rw_cells rsegs m1 A cs -> munch W m1 m2 -> wmono rsegs m1 m2 ->
    (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m2 A cs.
  Proof.
    intros W m1 m2 A cs [[Hwf HB] HW] MU WM Hout.
    split; [split; [exact Hwf|] | exact (wr_at_transport rsegs m1 m2 A _ HW WM)].
    apply (fl_bytes W m1 m2 A _ HB MU). rewrite (cells_bytes_length cs Hwf). exact Hout.
  Qed.

  (* The state carried through the six header stores: the header cells h at o + 12. *)
  Definition aH (jf : list byte) (mc : word -> option byte) (h : list cell) : Prop :=
    aJ mc /\ stk rsegs mc LO (SP0 + -128) /\ munch aWL m mc /\ wmono rsegs m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (SP0 + -128) (CB 24 jf :: aFT) /\
    rw_cells rsegs mc o [CB 6 db] /\ rw_cells rsegs mc (o + 6) [CB 6 sb] /\ rw_cells rsegs mc (o + 12) h /\
    rw_cells rsegs mc (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] /\
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] /\
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)].

  Lemma aH_ao : forall jf mc h, aH jf mc h -> addressable mc o LEN.
  Proof. intros jf mc h (AJ & _). destruct AJ as (_ & _ & _ & AO' & _). exact AO'. Qed.

  Lemma aH_ok : forall jf mc h k c a, aH jf mc h -> cell_at h k = Some c -> csize c = 1%nat ->
    a = o + 12 + Z.of_nat k -> store_ok rsegs mc (Z_to_bv 64 a) 1 = true.
  Proof.
    intros jf mc h k c a (_ & _ & _ & _ & _ & _ & _ & _ & P3 & _) Hcl Hs ->.
    exact (rw_cells_store_ok rsegs mc (o + 12) h k c 1 P3 Hcl (eq_sym Hs)).
  Qed.

  (* One checked header byte store at o + 12 + k. *)
  Lemma aH_st : forall jf mc h k c a (b : byte), EE = true -> aH jf mc h -> cells_size h = 6%nat ->
    cell_at h k = Some c -> csize c = 1%nat -> a = o + 12 + Z.of_nat k ->
    aH jf (write_to_mem mc (Z_to_bv 64 a) [b]) (cell_upd h k (C1 b)).
  Proof.
    intros jf mc h k c a b HE (AJ & ST & MU & WM & MI & FR & P1 & P2 & P3 & P4 & P5 & P6) Hsz Hcl Hs Ea.
    subst a.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof (cell_at_bound h k c Hcl) as Hkb. rewrite Hsz, Hs in Hkb.
    pose proof AJ as AJc. destruct AJc as (_ & _ & _ & AOm & _ & _).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    pose proof (rw_cells_store_ok rsegs mc (o + 12) h k c 1 P3 Hcl (eq_sym Hs)) as HS.
    change (Z_to_bv 64 (o + 12 + Z.of_nat k)) with (wa (o + 12 + Z.of_nat k)).
    unfold aH.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
    - apply (aJ_ostore mc _ b AJ API ART). lia.
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | cbn [length]; exact HS].
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
    - apply rw_cells_frame; [exact P1 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
    - apply rw_cells_frame; [exact P2 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
    - exact (rw_cells_write rsegs mc (o + 12) h k c (C1 b) P3 Hcl (eq_sym Hs) I).
    - apply rw_cells_frame; [exact P4 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
    - apply rw_cells_frame; [exact P5 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
    - apply rw_cells_frame; [exact P6 | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia].
  Qed.

  (* After the sb of a header byte: the next aH, in the memory named afresh. *)
  Ltac a_hstore HE AH k :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?A) [?bb]) _) =>
        let AH' := fresh "AH" in
        pose proof (aH_st _ mm _ k (C1 (Z_to_bv 8 0)) A bb HE AH eq_refl eq_refl eq_refl ltac:(lia)) as AH';
        cbn [cell_upd csize Nat.eqb Nat.sub] in AH';
        let m' := fresh "m" in
        set (m' := write_to_mem mm (Z_to_bv 64 A) [bb]) in *; clearbody m'; clear AH; rename AH' into AH
    end.

  (* The window of the ctrl_lay_block call inside this function's munch window (as in aJ_lay). *)
  Lemma alay_sub : 52 <= LEN ->
    sub_fp aWlay (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]).
  Proof.
    intros HLe. pose proof arng_sp as RSP.
    intros x Hx. cbn [outside app] in Hx. destruct Hx as (Hlo & Ho_ & Hrest).
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

  (* A byte of application memory apart from fp_w, the block and the callee window is outside aWlay. *)
  Lemma alay_out : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat] FS) x -> ~ (o + 18 <= x < o + 50) ->
    (x < SP0 + -128 - CTRL_LAY_BLOCK_K \/ SP0 + -128 <= x) -> outside aWlay x.
  Proof.
    intros x Hap Hfp Ho_ Hw. pose proof arng_sp as RSP.
    apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [exact Ho_|]. split; [|exact I]. intros [H1 H2]. destruct Hw; lia.
    - exact Hfp.
    - cbn [outside]. split; [|exact I]. apply alay_shout; [exact Hap | unfold CTRL_LAY_BLOCK_K; lia | lia].
  Qed.

  Lemma alay_outd : forall mc a b x, aJ mc -> In (a, b) aDL -> a <= x < b -> app_mem x ->
    ~ (o + 18 <= x < o + 50) -> (x < SP0 + -128 - CTRL_LAY_BLOCK_K \/ SP0 + -128 <= x) -> outside aWlay x.
  Proof.
    intros mc a b x AJ Hin Hx Hap Ho_ Hw. destruct AJ as (_ & _ & _ & _ & FPm & _).
    apply alay_out; [exact Hap | | exact Ho_ | exact Hw].
    exact (fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) a b x (fl_fp_dj _ _ _ _ _ _ _ _ FPm) Hin Hx).
  Qed.

  (* The saved-register frame [SP0 + -128, SP0) is outside aWlay. *)
  Lemma alay_outw : forall x, EE = true -> SP0 + -128 <= x < SP0 -> outside aWlay x.
  Proof.
    intros x HE Hx. pose proof arng_sp as RSP. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    assert (Hap : app_mem x).
    { pose proof (addressable_app m LO 4640 AWIN) as A0. apply A0. lia. }
    apply alay_out; [exact Hap | | | right; lia].
    - apply alay_outfpw_hi; [exact Hap | exact FSpos | exact Fmod | lia | lia].
    - destruct DsoLO; lia.
  Qed.

  (* The output apart from the block [o + 18, o + 50) is outside aWlay. *)
  Lemma alay_outo : forall mc x, EE = true -> aJ mc -> o <= x < o + LEN -> ~ (o + 18 <= x < o + 50) ->
    outside aWlay x.
  Proof.
    intros mc x HE AJ Hx Ho_.
    destruct (AO HE) as (AOo & _ & _). pose proof (addressable_app m o LEN AOo) as API.
    destruct (HEo HE) as (_ & DsoLO & _). unfold ly_dj in DsoLO.
    apply (alay_outd mc o (o + LEN) x AJ);
      [ cbn [In]; right; right; right; right; left; reflexivity | exact Hx | apply API; exact Hx | exact Ho_
      | destruct DsoLO; [right | left; unfold CTRL_LAY_BLOCK_K]; lia ].
  Qed.

  Lemma alay_outf : forall mc x, EE = true -> aJ mc -> f <= x < f + 24 -> outside aWlay x.
  Proof.
    intros mc x HE AJ Hx. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (addressable_app m f 24 Af) as AFI.
    destruct (HEo HE) as (_ & _ & Dof & _). unfold ly_dj in Dof.
    pose proof Dsf as Dsfu. unfold ly_dj in Dsfu.
    apply (alay_outd mc f (f + 24) x AJ);
      [ cbn [In]; left; reflexivity | exact Hx | apply AFI; exact Hx | lia
      | destruct Dsfu; [right | left; unfold CTRL_LAY_BLOCK_K]; lia ].
  Qed.

  (* row and its shadow bytes at the ctrl_lay_block call's return. *)
  Lemma alay_f : forall mc m1, EE = true -> aJ mc -> munch aWL m mc -> munch aWlay mc m1 ->
    bytes_at rsegs m1 f row /\ addressable m1 f 24.
  Proof.
    intros mc m1 HE AJ MU MU1.
    pose proof arng_sp as RSP. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof AJ as AJc. destruct AJc as (_ & _ & AWm & AOm & FPm & _).
    pose proof (addressable_app mc o LEN AOm) as API.
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    pose proof alay_fs as (FSpos & Fmod & Fapp & FSL).
    destruct (HEo HE) as (_ & _ & Dof & _).
    assert (MK : meta_kept m mc).
    { apply (munch_meta aWL m mc MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (HRc : bytes_at rsegs mc f row).
    { apply (em_obj rsegs m mc LO SP0 o LEN f row 24 MU HR ltac:(rewrite Hrl; reflexivity));
        [exact Dsf | exact Dof]. }
    assert (ADc : addressable mc f 24) by (apply (addressable_kept m mc f 24 Af MK)).
    split.
    - apply (fl_bytes aWlay mc m1 f row HRc MU1). rewrite Hrl. intros x Hx. apply (alay_outf mc x HE AJ). lia.
    - apply (alay_akeep aWlay mc m1 f 24 ADc MU1). intros i Hi.
      pose proof (addressable_app m f 24 Af) as AFI.
      pose proof Dsf as Dsfu. unfold ly_dj in Dsfu.
      apply (alay_sh (f + i));
        [ apply AFI; lia | exact API | exact AIwS | exact Fmod | exact Fapp
        | exact (fl_dj_out_r aDL (fp_w [0%nat; 1%nat] FS) f (f + 24) (f + i) (fl_fp_dj _ _ _ _ _ _ _ _ FPm)
                   ltac:(cbn [In]; left; reflexivity) ltac:(lia))
        | destruct Dsfu; [right | left; unfold CTRL_LAY_BLOCK_K]; lia
        | lia ].
  Qed.

  (* 0x84cdc .. 0x84cec, the end of the first stretch: the four argument moves a0 = o (s4), a1 = f (s3),
     a2 = md (s6), a3 = g (s8), and then the state the `jal` at 0x84cec hands to ctrl_lay_block.  This is the
     cut: the facts this run carries (aJ, the frame, the output cells) travel in aAtLay, and the call itself is
     not taken here. *)
  Lemma alay_pre : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                      (mc : word -> option byte) (j0 : list byte) (P : word),
    EE = true -> length j0 = 8%nat ->
    aJ mc -> stk rsegs mc LO (SP0 + -128) -> munch aWL m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] -> rw_cells rsegs mc (o + 12) [CB 6 HDR] ->
    rw_cells rsegs mc (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
               (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x84cdc) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc j0 P
      HE Lj0 AJ ST MU WM MI FR P1 P2 P3 P4 P5 P6.
    pose proof arng_sp as Rsp.
    (* addi a0,s4,0; addi a1,s3,0; addi a2,s6,0; addi a3,s8,0 *)
    do 4 step.
    apply evtF_done. right.
    exists x1, u0, u1, u2, x8, x9, x14, x15, x16, x17, u3, u4, u5, u6, mc, j0, P.
    split; [reflexivity|].
    split; [exact HE|]. split; [exact Lj0|]. split; [exact AJ|]. split; [exact ST|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|].
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    exact P6.
  Qed.

  (* The whole function's post from a stretch's LOCAL post: the local window aWL = [LO, SP0) and the output
     lies inside the cumulative window, and the two munch / wmono facts compose at the stretch's base memory
     mz.  The local window holds no fp_w [0; 1] FS range and no shadow range: no callee of a stretch that this
     lemma serves writes shadow bytes (their posts' munch windows are their frames and their data ranges), so
     a journal can cross it. *)
  Lemma aQp_of_local : forall (mz : word -> option byte) (ms' : machine_state),
    EE = true ->
    munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m mz ->
    wmono rsegs m mz ->
    aQg mz aWL ms' -> aQp ms'.
  Proof.
    intros mz ms' HE MU WM H.
    destruct H as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                   -> & MUl & WMl & MI' & ST' & AC' & SW' & AW' & FP' & RES).
    unfold aQp, aQg.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split.
    { rewrite HE. apply (munch_trans _ m mz m' MU).
      apply (munch_weaken aWL); [|exact MUl].
      intros x Hx. exact (proj1 (alay_oai aWL _ x Hx)). }
    split; [exact (wmono_trans rsegs m mz m' WM WMl)|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AC'|]. split; [exact SW'|].
    split; [exact AW'|]. split; [exact FP'|]. exact RES.
  Qed.

  (* The whole function's post from the early return's own post: its window, the real stack window alone, is
     inside the cumulative one, and its munch / wmono already start at m. *)
  Lemma aQp_of_win0 : forall ms' : machine_state, aQg m [(LO, SP0)] ms' -> aQp ms'.
  Proof.
    intros ms' H.
    destruct H as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                   -> & MUl & WMl & MI' & ST' & AC' & SW' & AW' & FP' & RES).
    unfold aQp, aQg.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split.
    { apply (munch_weaken [(LO, SP0)]); [|exact MUl].
      intros x Hx. destruct (alay_oai WW _ x Hx) as (H1 & _).
      cbn [outside] in H1 |- *. destruct H1 as (Ha & _). split; [exact Ha | exact I]. }
    split; [exact WMl|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AC'|]. split; [exact SW'|].
    split; [exact AW'|]. split; [exact FP'|]. exact RES.
  Qed.

  (* ---- THE SECOND STRETCH, the return point 0x84cf0 -> ret, RE-BASED on the return memory m5.
     0x84cf0 .. 0x84d24: the check of row[23] (at f + 23) and its load; the frame word ns at SP0 + -112; when
     row[23] <> 0, the reac_braid_encode call (0x84d20) with a2 = P, a4 = ns; then atail2 (the ctrl_finish call
     at 0x84d2c and the trailer), and the epilogue.
     EVERY premise is a fact AT m5, the memory ctrl_lay_block returns: no munch, no wmono and no cell of the
     memory before the call.  The core's astack_malloc_realizes gives only VIEW facts across that call
     (a Theorem Labs lane on lib/Reusable/YG0d.v:285-300), so a caller in cgif form can supply facts at m5 but cannot
     relate the two memories as raw memories.
     The conclusion is this stretch's OWN post aQg m5 aWL: the run writes only
     inside [LO, SP0) and the output [o, o + LEN), and allocates no fake-stack frame, so neither an
     fp_w [0; 1] FS range nor the stack-shadow range is in its window.  aQp_of_local turns it into the whole function's
     post for a caller that holds the cumulative munch / wmono from m. ---- *)
  Lemma ctrl_emit_as_post_lay_F :
    forall (x1 c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 : word)
           (m5 : word -> option byte) (j0 : list byte) (P : word),
    EE = true -> length j0 = 8%nat ->
    (* the state of the run at the return point, every fact AT m5 *)
    aJ m5 -> stk rsegs m5 LO (SP0 + -128) ->
    mem_inv rsegs m5 ->
    rw_cells rsegs m5 (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    bytes_at rsegs m5 f row -> addressable m5 f 24 ->
    rw_cells rsegs m5 o [CB 6 db] -> rw_cells rsegs m5 (o + 6) [CB 6 sb] ->
    rw_cells rsegs m5 (o + 12) [CB 6 HDR] -> rw_cells rsegs m5 (o + 18) [CB 32 LB] ->
    rw_cells rsegs m5 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs m5 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG (aQg m5 aWL)
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7
               (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
               (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) c3 c4 c5 c6)
          F (Z_to_bv 64 0x84cf0) fc None m5 (seg_rom rsegs)).
  Proof.
    intros x1 c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 m5 j0 P
      HE Lj0 AJ5 ST5' MI5 FR5 HR5 ADf5 P1' P2' P3' LB5 P5' P6'.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof AJ5 as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app m5 o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    pose proof DsoLO as DsoLOu. unfold ly_dj in DsoLOu.
    pose proof Af as Afl. destruct Afl as (Hfge & _ & _ & _).
    pose proof Amd as Amdl. destruct Amdl as (Hmdge & _ & _ & _).
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app m5 LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (HLe : 52 <= LEN) by lia.
    pose proof (fl_fp_dj _ _ _ _ _ _ _ _ FPm) as HDd.
    pose proof (rc_u8_range row 16) as R16. pose proof (rc_u8_range row 17) as R17.
    (* addi a0,s3,23; the check of f + 23; lbu a0,0(a0); ld a4,16(sp); beqz a0 *)
    pose proof (rd_byte rsegs m5 f row 23 HR5 ltac:(lia)) as RD23. change (Z.of_nat 23) with 23 in RD23.
    pose proof (rc_u8_range row 23) as R23.
    step.
    chk_go (f + 23) (Z_to_bv 5 12) (a_shadow m5 f 24 (f + 23) 23 ADf5 ltac:(lia) ltac:(lia)) no_extra.
    step. step. step.
    rewrite (rc_u8_eqb row 23 0) by lia.
    destruct (Z.eqb_spec (rc_u8 row 23) 0) as [A0|A0]; cbv iota.
    - eapply (atail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 m5
                (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)));
        [ exact HE | apply afr_merge; exact FR5 | exact ST5' | apply munch_refl | apply wmono_refl
        | exact MI5 | exact AJ5
        | exact HR5 | exact (addressable_sub m5 f 24 18 3 ADf5 ltac:(lia) ltac:(lia) ltac:(lia))
        | exact P1' | exact P2' | exact P3' | exact LB5 | exact P5' | exact P6' ].
    - assert (A1 : AA = 1) by (pose proof HA as HA'; unfold ubat in HA' |- *; unfold rc_u8 in A0, R23; lia).
      pose proof (Hns0 A1) as Hn0.
      (* addi a0,s4,50; mv a1,s2; ld a2,8(sp); mv a3,s2; jal reac_braid_encode *)
      do 5 step.
      destruct (stk_split rsegs m5 LO (SP0 + -128 - 48) (SP0 + -128) ST5' ltac:(lia)) as (STa & STb).
      eapply evtF_cut.
      { eapply HBR with (ns := ns);
        [ lia | reflexivity | rewrite Esp; unfold REAC_BRAID_ENCODE_FRAME; exact STb
        | rewrite Esp; unfold REAC_BRAID_ENCODE_FRAME;
          eapply rng_sub; [exact RWIN | lia | lia] ]. }
      intros ms' (m6 & -> & MU6 & WM6 & MI6 & ST6). fixret.
      rewrite Esp in MU6, ST6. unfold REAC_BRAID_ENCODE_FRAME in MU6, ST6.
      pose proof (MI6 MI5) as MI6'.
      assert (SUB6 : sub_fp [(SP0 + -128 - 48, SP0 + -128)] [(LO, SP0)]).
      { intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact I]. }
      pose proof (aJ_win _ m5 m6 AJ5 MU6 WM6 SUB6) as AJ6.
      (* the second stretch's own window, counted from m5 *)
      assert (ST6' : stk rsegs m6 LO (SP0 + -128)).
      { apply (stk_merge rsegs m6 LO (SP0 + -128 - 48) (SP0 + -128)); [| exact ST6 | lia].
        apply (stk_transport_disjoint rsegs [(SP0 + -128 - 48, SP0 + -128)] m5 m6 _ _ STa MU6 WM6).
        cbn [disjoint_from]. split; [lia | exact I]. }
      assert (DJ : forall Aq nq, Aq + nq <= SP0 + -128 - 48 \/ SP0 + -128 <= Aq ->
                     disjoint_from [(SP0 + -128 - 48, SP0 + -128)] Aq nq)
        by (intros Aq nq Hq; cbn [disjoint_from]; split; [lia | exact I]).
      assert (FR6 : rw_cells rsegs m6 (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT)).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ FR5 MU6 WM6). apply DJ. lia. }
      assert (P1'' : rw_cells rsegs m6 o [CB 6 db]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ P1' MU6 WM6). apply DJ. cbn [cells_size csize Nat.add]. lia. }
      assert (P2'' : rw_cells rsegs m6 (o + 6) [CB 6 sb]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ P2' MU6 WM6). apply DJ. cbn [cells_size csize Nat.add]. lia. }
      assert (P3'' : rw_cells rsegs m6 (o + 12) [CB 6 HDR]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ P3' MU6 WM6). apply DJ. cbn [cells_size csize Nat.add]. lia. }
      assert (P4'' : rw_cells rsegs m6 (o + 18) [CB 32 LB]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ LB5 MU6 WM6). apply DJ. cbn [cells_size csize Nat.add]. lia. }
      assert (P5'' : rw_cells rsegs m6 (o + 50)
                       [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ P5' MU6 WM6). apply DJ. cbn [cells_size csize]. lia. }
      assert (P6'' : rw_cells rsegs m6 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)]).
      { apply (rw_cells_transport rsegs _ m5 m6 _ _ P6' MU6 WM6). apply DJ. cbn [cells_size csize Nat.add]. lia. }
      assert (HR6 : bytes_at rsegs m6 f row).
      { apply (bytes_at_transport rsegs _ m5 m6 f row HR5 MU6). apply DJ. rewrite Hrl.
        pose proof Dsf as Dsfu. unfold ly_dj in Dsfu. lia. }
      assert (MK6 : meta_kept m5 m6).
      { apply (munch_meta _ m5 m6 MU6). cbn [all_app].
        split; [apply (app_ivl_sub LO SP0); [exact AIwS | lia | lia] | exact I]. }
      pose proof (addressable_kept m5 m6 f 24 ADf5 MK6) as ADf6.
      assert (MUb6 : munch aWL m5 m6).
      { apply (munch_weaken [(SP0 + -128 - 48, SP0 + -128)]); [|exact MU6].
        intros x Hx. cbn [outside app] in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact I]. }
      eapply (atail2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 m5
                (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)));
        [ exact HE | apply afr_merge; exact FR6 | exact ST6' | exact MUb6 | exact WM6
        | exact MI6' | exact AJ6
        | exact HR6 | exact (addressable_sub m6 f 24 18 3 ADf6 ltac:(lia) ltac:(lia) ltac:(lia))
        | exact P1'' | exact P2'' | exact P3'' | exact P4'' | exact P5'' | exact P6'' ].
  Qed.

  (* The continuation of atail_pre at 0x84c40: the six checked header byte stores (136, 25, the two bytes of a5,
     row[0], row[1] at o + 12 .. o + 17), then alay_pre. *)
  Lemma atail_k : forall (j0 : list byte) (P : word), length j0 = 8%nat -> EE = true ->
    forall (y1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (m2 : word -> option byte),
      aJ m2 -> stk rsegs m2 LO (SP0 + -128) -> munch aWL m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      rw_cells rsegs m2 (SP0 + -128) (CB 24 (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) :: aFT) ->
      bytes_at rsegs m2 f row -> addressable m2 f 24 ->
      rw_cells rsegs m2 o [CB 6 db] -> rw_cells rsegs m2 (o + 6) [CB 6 sb] ->
      rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
      rw_cells rsegs m2 (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
      rw_cells rsegs m2 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
      rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
      evtF rsegs RNG aMid
        (MS (mkR y1 (Z_to_bv 64 (SP0 + -128)) gp tp w0 w1 w2 (zxb (nth 1 row (Z_to_bv 8 0)))
                 (zxb (nth 0 row (Z_to_bv 8 0))) b0 b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
                 (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) w3 w4 w5 w6)
            F (Z_to_bv 64 0x84c40) fc None m2 (seg_rom rsegs)).
  Proof.
    intros j0 P Lj0 HE y1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m2
      AJ ST MU WM MI FR _ _ P1 P2 P3 P4 P5 P6.
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof (conj AJ (conj ST (conj MU (conj WM (conj MI (conj FR (conj P1 (conj P2
                  (conj (a6c _ _ _ P3) (conj P4 (conj P5 P6))))))))))) as AH.
    change (aH (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) m2
              [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
               C1 (Z_to_bv 8 0)]) in AH.
    clear AJ ST MU WM MI FR P1 P2 P3 P4 P5 P6.
    (* addi a0,s4,12; the check of o + 12; li a1,136; addi a0,s4,13; sb a1,12(s4) *)
    step.
    chk_go (o + 12) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 12) 12 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 0 (C1 (Z_to_bv 8 0)) (o + 12) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 0%nat. clear HS.
    (* the check of o + 13; li a1,25; addi a0,s4,14; sb a1,13(s4) *)
    chk_go (o + 13) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 13) 13 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 1 (C1 (Z_to_bv 8 0)) (o + 13) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 1%nat. clear HS.
    (* the check of o + 14; sb s5,14(s4); addi a0,s4,15 *)
    chk_go (o + 14) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 14) 14 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 2 (C1 (Z_to_bv 8 0)) (o + 14) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 2%nat. clear HS.
    step.
    (* the check of o + 15; srli a1,s5,8; addi a0,s4,16; sb a1,15(s4) *)
    chk_go (o + 15) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 15) 15 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 3 (C1 (Z_to_bv 8 0)) (o + 15) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 3%nat. clear HS.
    (* the check of o + 16; sb s1,16(s4); addi a0,s4,17 *)
    chk_go (o + 16) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 16) 16 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 4 (C1 (Z_to_bv 8 0)) (o + 16) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 4%nat. clear HS.
    step.
    (* the check of o + 17; sb s0,17(s4) *)
    chk_go (o + 17) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 17) 17 (aH_ao _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok _ _ _ 5 (C1 (Z_to_bv 8 0)) (o + 17) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 5%nat. clear HS.
    destruct AH as (AJh & STh & MUh & WMh & MIh & FRh & P1h & P2h & P3h & P4h & P5h & P6h).
    apply em_merge in P3h. cbn [cells_size csize cells_bytes cbytes app Nat.add] in P3h.
    rewrite (em_byte_lit 136), (em_byte_lit 25), em_c16_hi, (em_c16_lo a5), !em_byte_zxb in P3h by lia.
    pose proof (afr_split _ _ _ _ _ _ Lj0 FRh) as FRs.
    eapply alay_pre; [ exact HE | exact Lj0 | exact AJh | exact STh | exact MUh | exact WMh | exact MIh | exact FRs
                 | exact P1h | exact P2h | exact P3h | exact P4h | exact P5h | exact P6h ].
  Qed.

  (* atail: 0x84be4 -> aMid, with the frame word P at SP0 + -120 and ns at SP0 + -112. *)
  Lemma atail : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                       (mc : word -> option byte) (j0 : list byte) (P : word),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
               (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x84be4) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc j0 P HE FR ST MU WM MI AJ.
    assert (Lj0 : length j0 = 8%nat) by (destruct FR as [[Hwf _] _]; exact (proj1 Hwf)).
    exact (atail_pre x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc
             (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) (atail_k j0 P Lj0 HE) HE
             (afr_merge mc _ j0 P (Z_to_bv 64 ns) _ FR) ST MU WM MI AJ).
  Qed.

  (* ---- The front branches, from the end of the prologue (0x84a2c) to atail (0x84be4) or to the early return
     aepi0 (EE = false). Nothing is stored before 0x84ba8, so the frame at SP0 + -128 stays the prologue's
     CB 24 j :: aFT until agate2 stores P (t3) at +8 and ns (t4) at +16. ---- *)

  (* The runtime state aJ of the entry memory, in the EE = true regime. *)
  Lemma aJ0 : EE = true -> aJ m.
  Proof.
    intros HE. pose proof FP as FP'. rewrite HE in FP'.
    split; [exact HAC | split; [exact HSW | split; [exact AWIN | split; [exact (proj1 (AO HE)) |
      split; [exact FP' | exact FPT]]]]].
  Qed.

  (* The extra step of the check of a 4-byte load: addi r,r,3 after the andi. *)
  Ltac add3 X := step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia).

  (* agate2 (0x84b84 .. 0x84be4): a2 = 0 (md <> 0, so the catalogue load is skipped), the stores of P (t3) at
     SP0 + -120 and ns (t4) at SP0 + -112, s5 = a5, s9 = s and s10 = LEN (1492 when row[21] = 2, else
     36 n + 52); then atail. *)
  Lemma agate2 : forall (x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                        (j : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 (zxb (nth 21 row (Z_to_bv 8 0)))
               (Z_to_bv 64 0) x13 (Z_to_bv 64 s) a5 x16 x17 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) x21
               (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g) x25 x26 (Z_to_bv 64 ASAN_K) P (Z_to_bv 64 ns) u5 u6)
          F (Z_to_bv 64 0x84b84) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 mc j HE FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (rc_u8_range row 21) as R21.
    (* mv a0,s2; beqz a2 (taken); li a2,1; sd t3,8(sp); sd t4,16(sp); beq a1,a2 *)
    step. step. if_true. step. step. step. step.
    pose proof (aJ_win [(LO, SP0)] m _ (aJ0 HE) MU WM (ain_sub LO ltac:(lia))) as AJ.
    rewrite (rc_u8_eqb row 21 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 1) as [L1|L1]; cbv iota.
    - (* row[21] = 1: mv s5,a5; mv s9,a4; li a1,36; mul a0,a0,a1; addi s10,a0,52 *)
      assert (L2 : LL <> 2) by (unfold ubat; unfold rc_u8 in L1; lia).
      do 5 step.
      rewrite (em_len_word n (em_E_wok _ _ _ _ HE L2)).
      replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
        by (unfold em_len; replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact L2);
            reflexivity).
      eapply atail; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
    - (* li a0,2; bne a1,a0 *)
      step. step. rewrite (rc_u8_eqb row 21 2) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbn [negb]; cbv iota.
      + (* row[21] = 2: mv s5,a5; mv s9,a4; li s10,1492; j *)
        change (rc_u8 row 21) with (ubat row 21) in L2.
        do 4 step.
        replace (Z_to_bv 64 1492) with (Z_to_bv 64 LEN) by (unfold em_len; rewrite L2; reflexivity).
        eapply atail; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
      + (* row[21] = 0: mv a0,s2, then as row[21] = 1 *)
        change (rc_u8 row 21) with (ubat row 21) in L2.
        do 6 step.
        rewrite (em_len_word n (em_E_wok _ _ _ _ HE L2)).
        replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
          by (unfold em_len; replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact L2);
              reflexivity).
        eapply atail; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
  Qed.

  (* agate (0x84b48 .. 0x84b84): the check of f + 22 and the load of row[22]; when row[22] = 1, the check of the
     4-byte load at md + 56 and the load of em_hid mb, with the early return (s10 = 0) when it is 0; then
     agate2. *)
  Lemma agate : forall (x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                       (j : list byte),
    LL = 2 \/ em_wok n = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 (zxb (nth 21 row (Z_to_bv 8 0)))
               (Z_to_bv 64 0) x13 (Z_to_bv 64 s) a5 x16 x17 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) x21
               (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g) x25 x26 (Z_to_bv 64 ASAN_K) P (Z_to_bv 64 ns) u5 u6)
          F (Z_to_bv 64 0x84b48) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 mc j WL FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HM) as BM. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    pose proof Af as Afl. destruct Afl as (Hfge & Hfle & _ & _).
    pose proof Amd as Amdl. destruct Amdl as (Hmge & Hmle & _ & _).
    assert (MK : meta_kept m mc).
    { apply (munch_meta [(LO, SP0)] m mc MU). cbn [all_app]. split; [|exact I].
      pose proof (addressable_app m LO 4640 AWIN) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    pose proof (addressable_kept m mc f 24 Af MK) as ADf.
    pose proof (addressable_kept m mc md 296 Amd MK) as ADm.
    pose proof (em_obj0 rsegs m mc LO SP0 f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 22 HRc ltac:(lia)) as RD22. change (Z.of_nat 22) with 22 in RD22.
    pose proof (rc_u8_range row 22) as R22.
    (* addi a0,s3,22; the check of f + 22 *)
    step.
    chk_go (f + 22) (Z_to_bv 5 16) (a_shadow mc f 24 (f + 22) 22 ADf ltac:(lia) ltac:(lia)) no_extra.
    (* lbu a0,0(a0); li a3,1; bne a0,a3 *)
    step. step. step.
    rewrite (rc_u8_eqb row 22 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 22) 1) as [G1|G1]; cbn [negb]; cbv iota.
    - pose proof (em_obj0 rsegs m mc LO SP0 md mb 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm) as HMc.
      destruct (rc_rd4_opaque rsegs mc md mb 56 HMc ltac:(lia)) as (L4 & EL4 & RD56).
      change (Z.of_nat 56) with 56 in RD56.
      (* addi a0,s6,56; the check of the 4-byte load at md + 56 *)
      step.
      chk_go (md + 56) (Z_to_bv 5 16)
        (a_shadow4 mc md 296 (md + 56) 56 ADm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) add3.
      (* lw a0,0(a0); beqz a0 *)
      step. rewrite (em_lw_hid mb L4 EL4).
      step. pose proof (em_hid_range mb) as RH. rewrite em_eqb0 by lia.
      destruct (Z.eqb_spec (em_hid mb) 0) as [H0|H0]; cbv iota.
      + (* li s10,0; j to the epilogue *)
        step. step.
        apply amid_q.
        eapply aepi0; [apply em_E_false_g; assumption | eassumption ..].
      + eapply agate2; [apply em_E_true; [exact WL | right; exact H0] | eassumption ..].
    - eapply agate2; [apply em_E_true; [exact WL | left; exact G1] | eassumption ..].
  Qed.

  (* achk2 (0x84a7c .. 0x84b48), row[21] <> 2: the n test (2 <= n <= 40 and n even, else the early return with
     s10 = 0), md <> 0 and a2 = 0; then agate. *)
  Lemma achk2 : forall (x1 u0 u1 u2 x10 x12 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                       (j : list byte),
    LL <> 2 ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 (zxb (nth 21 row (Z_to_bv 8 0)))
               x12 x13 (Z_to_bv 64 s) a5 x16 x17 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) x21
               (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g) x25 x26 (Z_to_bv 64 ASAN_K) P (Z_to_bv 64 ns) u5 u6)
          F (Z_to_bv 64 0x84a7c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x12 x13 x16 x17 x21 x25 x26 P u5 u6 mc j L2 FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HM) as BM.
    (* addiw a0,s2,-41; li a2,-39; li s10,0; bltu a0,a2 *)
    step. step. step. step. rewrite em_wok_ltu by lia.
    destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
    - (* andi a0,s2,1; bnez a0 *)
      step. step. rewrite em_odd by lia.
      destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
      + (* beqz s6 (md <> 0); li a2,0; j *)
        step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
        cbv iota. step. step.
        eapply agate; [right | eassumption ..].
        unfold em_wok. rewrite Ev. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia).
        replace (n <=? 40) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + apply amid_q.
        eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]
                      | eassumption ..].
    - apply amid_q.
      eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
        by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
    - apply amid_q.
      eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
    - apply amid_q.
      eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
  Qed.

  (* afront (0x84a2c .. ), the first instruction after the prologue: s3 = f, the check of f + 21 (s4 = o before the
     branch) and the load of row[21]. row[21] = 2: md <> 0, a2 = 0, agate. row[21] = 0: the n test (the early
     return with s10 = 0), then md <> 0 and achk2. row[21] = 1: md <> 0 and achk2. *)
  Lemma afront : forall (x1 u0 u1 u2 x12 x13 x16 x17 x19 x20 x21 x25 x26 P u5 u6 : word)
                        (mc : word -> option byte) (j : list byte),
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) x12 x13
               (Z_to_bv 64 s) a5 x16 x17 (Z_to_bv 64 n) x19 x20 x21 (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 g) x25 x26 (Z_to_bv 64 ASAN_K) P (Z_to_bv 64 ns) u5 u6)
          F (Z_to_bv 64 0x84a2c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x12 x13 x16 x17 x19 x20 x21 x25 x26 P u5 u6 mc j FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof (bytes_at_bound _ _ _ _ HM) as BM. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    pose proof Af as Afl. destruct Afl as (Hfge & Hfle & _ & _).
    assert (MK : meta_kept m mc).
    { apply (munch_meta [(LO, SP0)] m mc MU). cbn [all_app]. split; [|exact I].
      pose proof (addressable_app m LO 4640 AWIN) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    pose proof (addressable_kept m mc f 24 Af MK) as ADf.
    pose proof (em_obj0 rsegs m mc LO SP0 f row 24 MU HR ltac:(rewrite Hrl; reflexivity) Dsf) as HRc.
    pose proof (rd_byte rsegs mc f row 21 HRc ltac:(lia)) as RD21. change (Z.of_nat 21) with 21 in RD21.
    pose proof (rc_u8_range row 21) as R21.
    (* mv s3,a1; addi a1,a1,21; the check of f + 21 (mv s4,a0 before the branch) *)
    step. step.
    chk_go (f + 21) (Z_to_bv 5 10) (a_shadow mc f 24 (f + 21) 21 ADf ltac:(lia) ltac:(lia)) no_extra.
    (* lbu a1,0(a1); li a0,2; beq a1,a0 *)
    step. step. step.
    rewrite (rc_u8_eqb row 21 2) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbv iota.
    - (* beqz s6 (md <> 0); li a2,0; j *)
      step. rewrite rc_eqb by lia. replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0).
      cbv iota. step. step.
      eapply agate; [left; exact L2 | eassumption ..].
    - (* bnez a1 *)
      step. rewrite (rc_u8_eqb row 21 0) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 0) as [L0|L0]; cbn [negb]; cbv iota.
      + (* row[21] = 0: addiw a0,s2,-41; li a2,-39; li s10,0; bltu a0,a2 *)
        step. step. step. step. rewrite em_wok_ltu by lia.
        destruct (Z.leb_spec 2 n) as [W1|W1]; destruct (Z.leb_spec n 40) as [W2|W2]; cbn [andb negb]; cbv iota.
        * (* andi a0,s2,1; bnez a0; then bnez s6 (md <> 0) *)
          step. step. rewrite em_odd by lia.
          destruct (Z.even n) eqn:Ev; cbn [negb]; cbv iota.
          -- step. rewrite rc_eqb by lia.
             replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
             eapply achk2; [exact L2 | eassumption ..].
          -- apply amid_q.
             eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]
                           | eassumption ..].
        * apply amid_q.
          eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
            by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
        * apply amid_q.
          eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
        * apply amid_q.
          eapply aepi0; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
      + (* row[21] = 1: bnez s6 (md <> 0) *)
        step. rewrite rc_eqb by lia.
        replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
        eapply achk2; [exact L2 | eassumption ..].
  Qed.

  (* ---- THE FIRST STRETCH, 0x849d8 -> the ctrl_lay_block call site 0x84cec (aMid).
     amain (0x849d8 .. 0x84a2c), the prologue: the 128-byte frame with the 13 saves [CB 24 j; s11 .. s0; ra] at
     SP0 + -128, the moves s8 = g, s2 = n, s7 = d, s6 = md, and the shadow offset s11 = ASAN_K from the runtime's
     cell (the GOT word at 0x9fad0 holds the cell's address 0xa8878); then afront.  The run ends either at the
     call site (aAtLay) or, when EE = false, at the early return, which is already at aQp. *)
  Lemma ctrl_emit_as_pre_lay_F : forall (t0 t1 t2 t3 t5 t6 : word),
    evtF rsegs RNG aMid
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x849d8) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6.
    pose proof arng_sp as Rsp.
    pose proof argk as RGK. pose proof arck as RCK.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* the runtime's cells and the shadow map are apart from the frame *)
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp + -128, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. clear - HHM Hx.
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    (* afront as a local fact; the store steps transport (and replace) every stk, bytes_at and mem_inv fact about
       m, so the Section's own facts about m leave the context first *)
    pose proof afront as AF. clear HST HR HM HD HSb MI0.
    (* addi sp,sp,-128; the 13 saves; mv s8,a7; mv s2,a6; mv s7,a3; mv s6,a2 *)
    carve_frame 128%nat ST. do 18 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    (* auipc a2; ld a2,184(a2) (the GOT word); ld s11,0(a2) (the shadow offset) *)
    do 3 step.
    clear RG RC HRT HRT1.
    eapply AF; [eassumption | eassumption | | eassumption | eassumption].
    exact (munch_weaken _ _ m m1 (ain_sub (SP0 + -128) ltac:(lia)) MU).
  Qed.

  (* ---- THE GLUE.  The whole run from the two stretches and ctrl_lay_block_contract_F: the first stretch to
     the call site, the one `jal` at 0x84cec (the only step this proof takes itself), the callee's contract
     across the call, and the second stretch from the return point 0x84cf0.  Nothing of the body is re-walked
     here, so the glue checks that the cut loses nothing. ---- *)
  Lemma amain_split : forall (t0 t1 t2 t3 t5 t6 : word),
    evtF rsegs RNG aQp
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 (Z_to_bv 64 n) (Z_to_bv 64 g) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
               (Z_to_bv 64 ns) t5 t6)
          F (Z_to_bv 64 0x849d8) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t5 t6.
    eapply evtF_cut; [exact (ctrl_emit_as_pre_lay_F t0 t1 t2 t3 t5 t6)|].
    intros ms0 [HQ | HAt]; [exact (evtF_done rsegs RNG aQp ms0 (aQp_of_win0 ms0 HQ))|].
    destruct HAt as (x1 & u0 & u1 & u2 & x8 & x9 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & mc & j0 & P &
                    -> & HE & Lj0 & AJ & ST & MU & WM & MI & FR & P1 & P2 & P3 & P4 & P5 & P6).
    pose proof arng_sp as Rsp. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    pose proof (ROB HE) as ROo.
    pose proof AJ as AJc. destruct AJc as (ACm & SWm & AWm & AOm & FPm & TLm).
    pose proof (addressable_app mc o LEN AOm) as API.
    destruct (AO HE) as (_ & _ & ART).
    destruct (HEo HE) as (_ & DsoLO & Dof & Dot & Dom & Don & Dod & Dos & Dog).
    pose proof DsoLO as DsoLOu. unfold ly_dj in DsoLOu.
    pose proof Af as Afl. destruct Afl as (Hfge & _ & _ & _).
    pose proof Amd as Amdl. destruct Amdl as (Hmdge & _ & _ & _).
    assert (AIwS : app_ivl LO SP0).
    { pose proof (addressable_app mc LO 4640 AWm) as A0. apply (app_ivl_sub LO (LO + 4640) LO SP0 A0); lia. }
    assert (MK : meta_kept m mc).
    { apply (munch_meta aWL m mc MU). cbn [all_app]. split; [exact AIwS | split; [exact API | exact I]]. }
    assert (HRc : bytes_at rsegs mc f row).
    { apply (em_obj rsegs m mc LO SP0 o LEN f row 24 MU HR ltac:(rewrite Hrl; reflexivity));
        [exact Dsf | exact Dof]. }
    assert (Esp : bv_unsigned (Z_to_bv 64 (SP0 + -128)) = SP0 + -128) by (apply unsigned_lit; lia).
    assert (HLe : 52 <= LEN) by lia.
    pose proof (fl_fp_dj _ _ _ _ _ _ _ _ FPm) as HDd.
    pose proof (rc_u8_range row 16) as R16. pose proof (rc_u8_range row 17) as R17.
    (* jal ctrl_lay_block (0x84cec): ctrl_lay_block(o, f, md, g) *)
    step.
    eapply evtF_cut.
    { eapply HLB with (p := o) (f := f) (md := md) (g := g) (FS := FS) (fr := row)
                      (ob := repeat (Z_to_bv 8 0) 32) (tb := tb) (mb := mb) (nb := nb) (gb := gb).
      all: rewrite ?Esp.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact Hg.
      - apply em_mod16; [exact HS16 | reflexivity].
      - unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia. exact ST.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ DsoLO); unfold CTRL_LAY_BLOCK_K; lia.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dsf); unfold CTRL_LAY_BLOCK_K; lia.
      - intros K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dst K)); unfold CTRL_LAY_BLOCK_K; lia.
      - intros G0 A0. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsg G0 A0)); unfold CTRL_LAY_BLOCK_K; lia.
      - intros K M0. split; [apply (em_dj_sub _ _ _ _ _ _ _ _ Dsm); unfold CTRL_LAY_BLOCK_K; lia|].
        intros B H1 H2.
        apply (em_dj_sub _ _ _ _ _ _ _ _ (Dsn (conj (conj K B) (conj H1 H2)))); unfold CTRL_LAY_BLOCK_K; lia.
      - exact Hf8.
      - exact Hf24.
      - exact Hrl.
      - exact HRc.
      - exact Hk.
      - exact Hao.
      - exact Htm.
      - lia.
      - lia.
      - exact P4.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ Dof); lia.
      - intros K. apply (em_dj_sub _ _ _ _ _ _ _ _ (Dot K)); lia.
      - intros K M0. apply (em_dj_sub _ _ _ _ _ _ _ _ Dom); lia.
      - intros K M0 B H1 H2. apply (em_dj_sub _ _ _ _ _ _ _ _ (Don (conj (conj K B) (conj H1 H2)))); lia.
      - intros K M0. split; [exact Hmd8|]. split; [exact Hml|]. split.
        + exact (em_obj rsegs m mc LO SP0 o LEN md mb 296 MU HM ltac:(rewrite Hml; reflexivity) Dsm Dom).
        + intros B H1 H2. pose proof (conj (conj K B) (conj H1 H2)) as NMc.
          destruct (Hnm NMc) as [NO NB]. split; [exact NO|].
          exact (em_obj rsegs m mc LO SP0 o LEN _ _ _ MU NB eq_refl (Dsn NMc) (Don NMc)).
      - intros G0 A0. destruct (Hgb G0 A0) as [GL GB]. split; [exact GL|]. split.
        + exact (em_obj rsegs m mc LO SP0 o LEN _ _ _ MU GB GL (Dsg G0 A0) (Dog G0 A0)).
        + apply (em_dj_sub _ _ _ _ _ _ _ _ (Dog G0 A0)); lia.
      - exact MI.
      - exact ACm.
      - exact SWm.
      - unfold CTRL_LAY_BLOCK_K. lia.
      - lia.
      - unfold CTRL_LAY_BLOCK_K. replace (SP0 + -128 - 4512) with LO by lia.
        apply (addressable_prefix mc LO 4640 4512 AWm). lia.
      - exact (addressable_kept m mc f 24 Af MK).
      - exact (addressable_sub mc o LEN 18 32 AOm ltac:(lia) ltac:(lia) ltac:(lia)).
      - apply API. lia.
      - lia.
      - intros K. exact (addressable_kept m mc _ _ (Atm K) MK).
      - intros G0 A0. split; [exact (addressable_kept m mc _ _ (Ag G0 A0) MK)|].
        destruct (APg G0 A0) as [AP1 AP2]. split; [exact AP1|]. split; [exact AP2|].
        apply API. pose proof Hao as Hao'. unfold ly_ao, ly_al in Hao', A0 |- *. lia.
      - intros K M0. split; [exact (addressable_kept m mc _ _ Amd MK)|].
        intros B H1 H2. exact (addressable_kept m mc _ _ (An (conj (conj K B) (conj H1 H2))) MK).
      - intros K. exact (addressable_kept m mc _ _ (AJ14 K) MK).
      - intros K. exact (addressable_kept m mc _ _ (AJ13 K) MK).
      - exact (alay_fp mc HLe FPm).
      - exact FPtm.
      - exact FPg.
      - intros K M0. split.
        + exact (proj1 (proj1 (fl_dj_cons _ _ _) (proj2 (proj1 (fl_dj_cons _ _ _) HDd)))).
        + intros B H1 H2. exact (FPn (conj (conj K B) (conj H1 H2))).
      - exact (alay_tls mc TLm).
      - exact RRB.
      - exact RIMG.
      - exact arrt.
      - eapply rng_sub; [exact RWIN | unfold CTRL_LAY_BLOCK_K; lia | unfold CTRL_LAY_BLOCK_K; lia].
      - unfold sh_cover, sh_len, sh_lo.
        exact (RWSH (SP0 + -128 - CTRL_LAY_BLOCK_K) (SP0 + -128 - CTRL_LAY_BLOCK_K + CTRL_LAY_BLOCK_K - 1)
                 ltac:(unfold CTRL_LAY_BLOCK_K; lia) ltac:(unfold CTRL_LAY_BLOCK_K; lia)).
      - exact (proj1 (tp_rng_of_rtls _ _ _ _ _ _ _ _ _ FP RTLS)).
      - exact (proj2 (tp_rng_of_rtls _ _ _ _ _ _ _ _ _ FP RTLS)).
      - apply tls_rng_of_rtls. exact (a_rtls mc aWL HE MU ltac:(intros y Hy; exact Hy)).
      - exact RFS.
      - apply fs_frame_shadow_rng; [left; reflexivity | exact (RFSH FS (FS + FS_SIZE - 1) ltac:(lia) ltac:(lia))].
      - apply fs_frame_shadow_rng; [right; reflexivity | exact (RFSH FS (FS + FS_SIZE - 1) ltac:(lia) ltac:(lia))].
      - eapply rng_sub; [exact ROo | lia | lia].
      - unfold sh_cover, sh_len, sh_lo. exact (ROBS HE (o + 18) (o + 18 + 32 - 1) ltac:(lia) ltac:(lia)).
      - exact RROW.
      - unfold sh_cover, sh_len, sh_lo. exact (RROWS f (f + 24 - 1) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 2) as [K|K]; [right | left; exact K].
        split; [exact (RTM K)|]. unfold sh_cover, sh_len, sh_lo.
        exact (RTMS K (ly_tm row) (ly_tm row + 32 - 1) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec g 0) as [G0|G0]; [left; exact G0 | right].
        destruct (Z.eq_dec (ly_al row) 0) as [A0|A0]; [left; exact A0 | right].
        split; [exact (RGB G0 A0)|]. unfold sh_cover, sh_len, sh_lo.
        exact (RGBS G0 A0 g (g + ly_al row - 1) ltac:(lia) ltac:(lia)).
      - right; right. split; [exact RMD|]. unfold sh_cover, sh_len, sh_lo.
        exact (RMDS md (md + 296 - 1) ltac:(lia) ltac:(lia)).
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
        all: split; [exact (RNB NMc)|]; unfold sh_cover, sh_len, sh_lo.
        all: exact (RNBS NMc (rname mb) (rname mb + Z.of_nat (length nb) - 1) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 5) as [K5|K5]; [right | left; exact K5].
        split; [eapply rng_sub; [exact RIMG | unfold JOIN_0014; lia | unfold JOIN_0014; lia]|].
        unfold sh_cover, sh_len, sh_lo. exact (RJ14S K5 JOIN_0014 (JOIN_0014 + 32 - 1) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (ly_k row) 6) as [K6|K6]; [right | left; exact K6].
        split; [eapply rng_sub; [exact RIMG | unfold JOIN_0013; lia | unfold JOIN_0013; lia]|].
        unfold sh_cover, sh_len, sh_lo. exact (RJ13S K6 JOIN_0013 (JOIN_0013 + 32 - 1) ltac:(lia) ltac:(lia)). }
    intros ms' (c0 & c1 & c2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & c3 & c4 & c5 & c6 & m5 & -> &
                MU5 & WM5 & MI5 & ST5 & LB5 & AC5 & SW5 & AW5 & FP5 & _).
    rewrite Esp in MU5, ST5, AW5, FP5.
    fixret.
    (* 0x84cf0: the second stretch, re-based on the memory ctrl_lay_block returns.  The glue owns the step
       from the call's post to that memory's own facts, and aQp_of_local turns the stretch's local post into
       the whole function's post. *)
    pose proof (aJ_lay mc m5 _ _ HE HLe AJ MU5 AC5 SW5 AW5 FP5) as AJ5.
    assert (MUf : munch (aWL ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m5).
    { apply (munch_trans _ m mc m5).
      - apply (munch_weaken aWL); [intros x Hx; exact (proj1 (alay_oai aWL _ x Hx)) | exact MU].
      - apply (munch_weaken aWlay); [exact (alay_sub HLe) | exact MU5]. }
    assert (WMf : wmono rsegs m m5) by (exact (wmono_trans rsegs m mc m5 WM WM5)).
    destruct (alay_f mc m5 HE AJ MU MU5) as (HR5 & ADf5).
    assert (ST5' : stk rsegs m5 LO (SP0 + -128)).
    { unfold CTRL_LAY_BLOCK_K in ST5. replace (SP0 - 4640) with (SP0 + -128 - 4512) by lia. exact ST5. }
    assert (FR5 : rw_cells rsegs m5 (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT)).
    { apply (a_rwtr aWlay mc m5 _ _ FR MU5 WM5). cbn [cells_size csize Nat.add]. intros x Hx.
      apply (alay_outw x HE). lia. }
    assert (P1' : rw_cells rsegs m5 o [CB 6 db]).
    { apply (a_rwtr aWlay mc m5 _ _ P1 MU5 WM5). cbn [cells_size csize Nat.add]. intros x Hx.
      apply (alay_outo mc x HE AJ); lia. }
    assert (P2' : rw_cells rsegs m5 (o + 6) [CB 6 sb]).
    { apply (a_rwtr aWlay mc m5 _ _ P2 MU5 WM5). cbn [cells_size csize Nat.add]. intros x Hx.
      apply (alay_outo mc x HE AJ); lia. }
    assert (P3' : rw_cells rsegs m5 (o + 12) [CB 6 HDR]).
    { apply (a_rwtr aWlay mc m5 _ _ P3 MU5 WM5). cbn [cells_size csize Nat.add]. intros x Hx.
      apply (alay_outo mc x HE AJ); lia. }
    assert (P5' : rw_cells rsegs m5 (o + 50)
                    [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))]).
    { apply (a_rwtr aWlay mc m5 _ _ P5 MU5 WM5). cbn [cells_size csize]. intros x Hx.
      apply (alay_outo mc x HE AJ); lia. }
    assert (P6' : rw_cells rsegs m5 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)]).
    { apply (a_rwtr aWlay mc m5 _ _ P6 MU5 WM5). cbn [cells_size csize Nat.add]. intros x Hx.
      apply (alay_outo mc x HE AJ); lia. }
    apply (evtF_mono rsegs RNG (aQg m5 aWL) aQp);
      [|intros ms2 H2; exact (aQp_of_local m5 ms2 HE MUf WMf H2)].
    eapply ctrl_emit_as_post_lay_F with (m5 := m5) (j0 := j0) (P := P);
      [ exact HE | exact Lj0 | exact AJ5 | exact ST5' | exact MI5 | exact FR5 | exact HR5 | exact ADf5
      | exact P1' | exact P2' | exact P3' | exact LB5 | exact P5' | exact P6' ].
  Qed.

End Emit.

(* The whole-function footprint statement again, this time from the two stretches and the callee contract of
   ctrl_lay_block alone: ctrl_emit_as_pre_lay_F runs 0x849d8 -> the call site 0x84cec (or straight to the
   early return), ctrl_lay_block_contract_F crosses the call, and ctrl_emit_as_post_lay_F runs 0x84cf0 -> ret.
   The statement is the one ctrl_emit_asF.v proves as ctrl_emit_as_holds_F: the split loses nothing. *)
Theorem ctrl_emit_as_holds_F_of_split :
  asan_memset_cF.asan_memset_contract_F -> asan_memcpy_cF.asan_memcpy_contract_F -> ctrl_lay_block_contract_F ->
  reac_braid_encode_ns0_contract_F -> ctrl_finish_contract_F -> ctrl_emit_as_contract_F.
Proof.
  intros HMS HMC HLB HBR HFN. unfold ctrl_emit_as_contract_F, CTRL_EMIT_AS, CTRL_EMIT_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  cbv zeta.
  intros -> -> -> -> -> -> -> ->.
  intros Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR Hk Hc HL HG HA Hao Htm Hc2 HLA
    Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  intros RRB RIMG RWIN RWSH0 RFS RFSH0 RTLS RROW RROWS0 RMD RMDS0 RDB RDBS0 RSB RSBS0 RTM0 RNB0 RGB0 ROB0 RJ140
    RJ130.
  (* the ground 8-aligned covers of the contract, as the quantified premises the Section takes *)
  assert (RWSH : forall p q, bv_unsigned sp - 4640 <= p -> q <= bv_unsigned sp - 1 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RWSH0 Hp Hq)).
  assert (RFSH : forall p q, FS <= p -> q <= FS + FS_SIZE - 1 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RFSH0 Hp Hq)).
  assert (RROWS : forall p q, f <= p -> q <= f + 23 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RROWS0 Hp Hq)).
  assert (RMDS : forall p q, md <= p -> q <= md + 295 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RMDS0 Hp Hq)).
  assert (RDBS : forall p q, d <= p -> q <= d + 5 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RDBS0 Hp Hq)).
  assert (RSBS : forall p q, s <= p -> q <= s + 5 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros p q Hp Hq; exact (em_shcov_sub RNG _ _ p q RSBS0 Hp Hq)).
  assert (RTM : ly_k row = 2 -> rng RNG (ly_tm row) 32) by (intros K; exact (proj1 (RTM0 K))).
  assert (RTMS : ly_k row = 2 -> forall p q, ly_tm row <= p -> q <= ly_tm row + 31 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros K p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (proj2 (RTM0 K)) Hp Hq)).
  assert (RNB : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\
                rname mb <> 0 -> rng RNG (rname mb) (Z.of_nat (length nb)))
    by (intros K; exact (proj1 (RNB0 K))).
  assert (RNBS : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\
                 rname mb <> 0 -> forall p q, rname mb <= p -> q <= rname mb + Z.of_nat (length nb) - 1 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros K p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (proj2 (RNB0 K)) Hp Hq)).
  assert (RGB : g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row))
    by (intros G0 A0; exact (proj1 (RGB0 G0 A0))).
  assert (RGBS : g <> 0 -> ly_al row <> 0 -> forall p q, g <= p -> q <= g + ly_al row - 1 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros G0 A0 p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (proj2 (RGB0 G0 A0)) Hp Hq)).
  assert (ROB : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true -> rng RNG o (em_len (ubat row 21) n))
    by (intros HE; exact (proj1 (ROB0 HE))).
  assert (ROBS : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true ->
            forall p q, o <= p -> q <= o + em_len (ubat row 21) n - 1 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros HE p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (proj2 (ROB0 HE)) Hp Hq)).
  assert (RJ14S : ly_k row = 5 -> forall p q, JOIN_0014 <= p -> q <= JOIN_0014 + 31 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros K p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (RJ140 K) Hp Hq)).
  assert (RJ13S : ly_k row = 6 -> forall p q, JOIN_0013 <= p -> q <= JOIN_0013 + 31 ->
            rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8))
    by (intros K p q Hp Hq; exact (em_shcov_sub RNG _ _ p q (RJ130 K) Hp Hq)).
  clear RWSH0 RFSH0 RROWS0 RMDS0 RDBS0 RSBS0 RTM0 RNB0 RGB0 ROB0 RJ140 RJ130.
  eapply amain_split; eassumption.
Qed.

(* The three tops of this file rest on nothing but the semantics' own axioms (the build log shows the list). *)
Print Assumptions ctrl_emit_as_pre_lay_F.
Print Assumptions ctrl_emit_as_post_lay_F.
Print Assumptions ctrl_emit_as_holds_F_of_split.
