(* Route (C) (a Theorem Labs lane, 2026-10-29 09:20Z) forms of the two stretches of ctrl_emit_as (image A) that
   ctrl_emit_asF2.v proves (that file is unchanged apart from comment text; this one is additive, form ruling of a Theorem Labs lane):
     - ctrl_emit_as_pre_lay_F_on : ctrl_emit_asF2.ctrl_emit_as_pre_lay_F with aMid -> aMid_on;
     - ctrl_emit_as_post_lay_F_on: ctrl_emit_asF2.ctrl_emit_as_post_lay_F with aJ -> aJ_on and aQg -> aQg_on.
   Section EmitOn takes Section Emit's Variables and Hypotheses, same names, same order, except:
     - HMS / HMC / HFN are a Theorem Labs lane's asan_memset_cF_on.asan_memset_contract_F_on and
       asan_memcpy_cF_on.asan_memcpy_contract_F_on, and ctrl_finish_c.ctrl_finish_contract_F_on (a Theorem Labs lane; its
       shadow_rw premise is dropped);
     - HSW (the universal A.AsanRT.shadow_rw m) is the REGIONAL A.ShadowRwOn.shadow_rw_on Rsh m, with HRsh: Rsh
       holds the 8-aligned shadow-word span (sh_word_on.v) of the output [o, o + LEN) when EE = true, of the
       6-byte source d and of the 6-byte source s.  These are the spans the three helper calls of the first
       stretch read (memset o LEN, memcpy o d 6, memcpy (o + 6) s 6; em_sh_word_on_sub puts each sub-span of
       the output inside the output's span).
   aJ_on / aQg_on / aAtLay_on / aMid_on are aJ / aQg / aAtLay / aMid with `shadow_rw X` replaced by
   `A.ShadowRwOn.shadow_rw_on Rsh X`, conjunct order unchanged.  The inline ASan checks read the shadow from
   `addressable` (ctrl_emit_asF2.a_shadow), so Rsh is carried, not read: across the run's own stores and across
   each callee by A.ShadowRwOnK.fl_shadow_rw_on (every munch window here holds no shadow byte), and the helper
   calls' posts are not needed for it.
   The scripts are ctrl_emit_asF2.v's, with those changes only; the lemmas of ctrl_emit_asF2.v that mention
   neither shadow_rw nor a changed hypothesis are REUSED, qualified (the Local Abbreviations at the head of the
   Section instantiate them at this Section's variables).
   PROVENANCE: as ctrl_emit_asF2.v (image root lib/A/Img0.v, the asan build A of libreac v1.9.0, entry 0x849d8,
   the cut at the ctrl_lay_block call 0x84cec, the return point 0x84cf0). *)
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
(* Kept qualified: the route (C) contract texts of the two helpers and their shadow regions, the region itself, and
   the cut-form stretches whose shadow-free lemmas this file reuses. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan sh_word_on asan_memcpy_c_on asan_memset_c_on
  asan_memcpy_cF_on asan_memset_cF_on ctrl_emit_asF2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ShadowRwOnK.
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

Local Ltac fixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.


(* The shadow address is a division, which lia only sees after Z.div_mod_to_equations.  The Section's own shadow
   premises are quantified over their endpoints (a Theorem Labs lane, 2026-10-27 17:42Z: no ground division bound in a lemma's
   context), so this runs on small goals only. *)
Local Ltac dlia := first [ lia | (Z.div_mod_to_equations; lia) ].

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

(* A sub-span's shadow words lie in the span's: sh_word_on (sh_word_on.v) is monotone in its byte range. *)
Lemma em_sh_word_on_sub : forall p n p' n' a, p <= p' -> p' + n' <= p + n -> n <> 0 ->
  sh_word_on.sh_word_on p' n' a -> sh_word_on.sh_word_on p n a.
Proof.
  intros p n p' n' a H1 H2 Hn (_ & Ha1 & Ha2). split; [exact Hn|].
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
  pose proof (Z.div_le_mono p p' 8 ltac:(lia) H1) as D1.
  pose proof (Z.div_le_mono (p' + n' - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.div_le_mono (p / 8 + ASAN_K) (p' / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_le_mono ((p' + n' - 1) / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D4.
  lia.
Qed.

Section EmitOn.
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

  Hypothesis HMS_on : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMC_on : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HLB : ctrl_lay_block_contract_F.
  Hypothesis HBR : reac_braid_encode_ns0_contract_F.
  Hypothesis HFN_on : ctrl_finish_c.ctrl_finish_contract_F_on.
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
  (* Route (C): the shadow bytes this run needs present, as a region (in place of Section Emit's HSW). *)
  Variable Rsh : Z -> Prop.
  Hypothesis HSW_on : A.ShadowRwOn.shadow_rw_on Rsh m.
  Hypothesis HRsh : forall a, (EE = true /\ sh_word_on.sh_word_on o LEN a) \/ sh_word_on.sh_word_on d 6 a \/
                              sh_word_on.sh_word_on s 6 a -> Rsh a.
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

  (* ctrl_emit_asF2.v's lemmas and definitions that mention neither shadow_rw nor a changed hypothesis, at this
     Section's variables (the arguments are those `About` names after Section Emit closes). *)
  Local Abbreviation ashb :=
    (ctrl_emit_asF2.ashb sp o f md g n row mb db sb RNG Hg Hrl Hml Hdb Hsb RROWS RMDS ROBS).
  Local Abbreviation argk := (ctrl_emit_asF2.argk sp f md g row mb db sb RNG Hg Hrl Hml Hdb Hsb RIMG).
  Local Abbreviation arck := (ctrl_emit_asF2.arck sp f md g row mb db sb RNG Hg Hrl Hml Hdb Hsb RIMG).
  Local Abbreviation aimg := (ctrl_emit_asF2.aimg sp f md g row mb db sb RNG Hg Hrl Hml Hdb Hsb RIMG).
  Local Abbreviation acpy_shw := (ctrl_emit_asF2.acpy_shw RNG).
  Local Abbreviation aset_shw := (ctrl_emit_asF2.aset_shw RNG).
  Local Abbreviation aRES := (ctrl_emit_asF2.aRES a5 o md g n row tb mb nb gb db sb).
  Local Abbreviation arng_sp := (ctrl_emit_asF2.arng_sp sp m f md g row mb db sb Hg HST Hrl Hml Hdb Hsb).
  Local Abbreviation ain_sub := (ctrl_emit_asF2.ain_sub sp f md g row mb db sb Hg Hrl Hml Hdb Hsb).
  Local Abbreviation aTL := (ctrl_emit_asF2.aTL sp tp FS).
  Local Abbreviation a_shadow := ctrl_emit_asF2.a_shadow.
  Local Abbreviation a_shadow4 := (ctrl_emit_asF2.a_shadow4 sp f md g row mb db sb Hg Hrl Hml Hdb Hsb).
  Local Abbreviation alay_fs := (ctrl_emit_asF2.alay_fs sp tp m o f md d s n FS row mb FP).
  Local Abbreviation afr_merge := ctrl_emit_asF2.afr_merge.
  Local Abbreviation afr_split := ctrl_emit_asF2.afr_split.
  Local Abbreviation a6c := ctrl_emit_asF2.a6c.
  Local Abbreviation em_shspan := ctrl_emit_asF2.em_shspan.

  Ltac sh_in := first [ left; lia | right; left; lia | right; right; split; [assumption | lia] ].

  (* The shadow spans the helper calls of the first stretch read are inside Rsh: __asan_memset's (the output,
     o LEN) and each __asan_memcpy's (a 6-byte source, d or s, and a 6-byte sub-span of the output). *)
  Lemma aR_set : EE = true -> forall (a0 a2 : word), bv_unsigned a0 = o -> bv_unsigned a2 = LEN ->
    forall a, asan_memset_c_on.asan_memset_shadow_R a0 a2 a -> Rsh a.
  Proof.
    intros HE a0 a2 E0 E2 a Ha. unfold asan_memset_c_on.asan_memset_shadow_R in Ha. rewrite E0, E2 in Ha.
    apply HRsh. left. split; [exact HE | exact Ha].
  Qed.

  Lemma aR_cpy : EE = true -> forall (a0 a1 a2 : word) p q, bv_unsigned a0 = p -> bv_unsigned a1 = q ->
    bv_unsigned a2 = 6 -> o <= p -> p + 6 <= o + LEN -> q = d \/ q = s ->
    forall a, asan_memcpy_c_on.asan_memcpy_shadow_R a0 a1 a2 a -> Rsh a.
  Proof.
    intros HE a0 a1 a2 p q E0 E1 E2 Hp1 Hp2 Hq a Ha. pose proof (em_len_rng _ _ _ _ HE) as RLN.
    unfold asan_memcpy_c_on.asan_memcpy_shadow_R in Ha. rewrite E0, E1, E2 in Ha. apply HRsh.
    destruct Ha as [Ha|Ha].
    - right. destruct Hq as [-> | ->]; [left | right]; exact Ha.
    - left. split; [exact HE|]. exact (em_sh_word_on_sub o LEN p 6 a Hp1 Hp2 ltac:(lia) Ha).
  Qed.

  (* The post of a run that ends at ret, with its munch window W counted from a base memory mb.  The whole
     function takes mbz = m and the cumulative window (ctrl_emit_asF2.aQp); the
     second stretch takes mbz = the memory ctrl_lay_block returns and its OWN window, which holds no
     fp_w [0; 1] FS range because that stretch allocates no fake-stack frame. *)
  Definition aQg_on (mbz : word -> option byte) (W : list ivl) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch W mbz m'
      /\ wmono rsegs mbz m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ A.ShadowRwOn.shadow_rw_on Rsh m' /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (EE = true -> aRES m').

  (* The bundled runtime state carried across the body (EE = true regime: the output is [o, o + LEN)). *)
  Local Abbreviation aWL := [(LO, SP0); (o, o + LEN)].
  Local Abbreviation aDL := [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + LEN)].
  Definition aJ_on (mc : word -> option byte) : Prop :=
    asan_cells mc /\ A.ShadowRwOn.shadow_rw_on Rsh mc /\ addressable mc LO 4640 /\ addressable mc o LEN /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 aWL aDL /\ aTL mc.

  (* aJ_on survives writes inside the window [LO, SP0). *)
  Lemma aJ_win_on : forall W' m1 m2, aJ_on m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(LO, SP0)] -> aJ_on m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & AWo & FPc & TL) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split; [|split; [|split]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (A.ShadowRwOnK.fl_shadow_rw_on Rsh W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W' FPc MU WM Hs).
    - exact (fl_tls _ m1 m2 (bv_unsigned tp) FS LO SP0 _ aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* aJ_on survives writes inside the output [o, o + LEN), when the output is application memory apart from the
     runtime's cells and the side stack's bytes read back after the run. *)
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
    - exact (A.ShadowRwOnK.fl_shadow_rw_on Rsh W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM SWW RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU SWW TL).
  Qed.

  (* The asan facts in a memory that differs from m only inside the window [LO, SP0). *)
  Lemma atr_on : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ A.ShadowRwOn.shadow_rw_on Rsh mc /\ fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p q, addressable m p q -> addressable mc p q).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split]].
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (A.ShadowRwOnK.fl_shadow_rw_on Rsh W' m mc HSW_on MU WM SHo).
    - exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
    - intros p q H. exact (fl_addressable W' m mc p q H MU SHo).
  Qed.

  (* The epilogue (+0x394 .. +0x3d0): the return value RR, the register restores and ret.  It writes nothing,
     so the base memory mbz and the window W are the ones its caller hands in: the whole run takes mb = m with
     the cumulative window, the second stretch takes mbz = the memory ctrl_lay_block returns with its own. *)
  Lemma aepi_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (W : list ivl) (j : list byte) (r : Z),
    r = RR -> 0 <= r < 2^64 ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch W mbz mc -> wmono rsegs mbz mc -> mem_inv rsegs mc ->
    asan_cells mc -> A.ShadowRwOn.shadow_rw_on Rsh mc -> addressable mc LO 4640 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD ->
    (EE = true -> aRES mc) ->
    evtF rsegs RNG (aQg_on mbz W)
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 r) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d6c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc mbz W j r Er Rr FR ST MU WM MI AC SW AW FP' HRES.
    pose proof arng_sp as Rsp.
    pose proof ST as (Rlo & _ & _).
    do 16 step.
    apply evtF_done. unfold aQg_on.
    do 14 eexists. exists mc. rewrite Er.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP'|].
    exact HRES.
  Qed.

  (* The early return (EE = false): go to the epilogue with RR = 0 and no block written.  This path calls
     nothing, so its window is the real stack window alone: no side-stack range and no shadow range. *)
  Lemma aepi0_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    EE = false ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG (aQg_on m [(LO, SP0)])
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 x24 x25 (Z_to_bv 64 0) x27 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84d6c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 u3 u4 u5 u6
      mc j HE FR ST MU WM MI.
    pose proof arng_sp as Rsp.
    destruct (atr_on _ mc MU WM (ain_sub LO ltac:(lia))) as (AC & SW & FP' & ADT).
    apply (aepi_on x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
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
     a Theorem Labs lane's route (C) asan_memset_cF_on / asan_memcpy_cF_on). ----

     aAtLay_on: the state at the call site, with the registers and the memory the call receives: a0 = o, a1 = f,
     a2 = md, a3 = g (the four addi at 0x84cdc .. 0x84ce8, the state just before the `jal`), this function's
     frame at SP0 + -128 and the output as the checked memset and the two checked memcpy left it.  Every fact
     the premises of ctrl_lay_block_contract_F are built from travels in it; nothing else crosses the cut. *)
  Definition aAtLay_on : machine_state -> Prop :=
    fun ms' => exists (x1 u0 u1 u2 x8 x9 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                      (mc : word -> option byte) (j0 : list byte) (P : word),
      ms' = MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 x8 x9
                    (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g) x14 x15 x16 x17
                    (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d)
                    (Z_to_bv 64 g) (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
               F (Z_to_bv 64 0x84cec) fc None mc (seg_rom rsegs)
      /\ EE = true /\ length j0 = 8%nat /\ aJ_on mc /\ stk rsegs mc LO (SP0 + -128)
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
     journal can cross it.  The glue widens it to the whole function's post. *)
  Definition aMid_on : machine_state -> Prop :=
    fun ms' => aQg_on m [(LO, SP0)] ms' \/ aAtLay_on ms'.

  Lemma amid_q_on : forall ms', evtF rsegs RNG (aQg_on m [(LO, SP0)]) ms' -> evtF rsegs RNG aMid_on ms'.
  Proof.
    intros ms' H. apply (evtF_mono rsegs RNG (aQg_on m [(LO, SP0)]) aMid_on ms' H).
    intros x Hx. left. exact Hx.
  Qed.

  (* aJ_on survives a single 1-byte data store inside the output [o, o + LEN): the side stack reads back because the
     write keeps every byte of [FS, FS + FS_SIZE) defined (stk_write). *)
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

  (* aJ_on survives a callee's writes whose window is inside the window and the output together ([LO, SP0) U
     [o, o + LEN)), when the side stack's bytes read back after the call. *)
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
    - exact (A.ShadowRwOnK.fl_shadow_rw_on Rsh W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_addressable W' m1 m2 _ _ AWo MU SHo).
    - exact (fl_fp_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W' FPc MU WM Hs RD).
    - exact (fl_tls_W _ m1 m2 (bv_unsigned tp) FS LO SP0 aWL aDL W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) FPc MU Hs TL).
  Qed.

  (* The em_fr trailer (0x84d30 .. 0x84d6c): s4 := o + LEN, then the two checked trailing stores (194 at
     o + LEN - 2, -22 at o + LEN - 1), then the epilogue via aepi_on. *)
  Lemma atail3_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25
                        u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL mbz mc ->
    wmono rsegs mbz mc -> mem_inv rsegs mc -> aJ_on mc ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 BLK] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    (CC = 1 \/ CC = 2 -> closes CC RO RL BLK /\ (closes CC RO RL LB -> BLK = LB)) ->
    evtF rsegs RNG (aQg_on mbz aWL)
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
    eapply aepi_on.
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
    - intros _. unfold ctrl_emit_asF2.aRES. split; [|split].
      + exact (em_fr_bytes rsegs m2 o LEN db sb BLK (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0))
                 (nth 1 row (Z_to_bv 8 0)) P1' P2' P3' P4' P5' HBF ltac:(lia)).
      + intros HL2. exact (em_E_wok _ _ _ _ HE HL2).
      + exact CLS.
  Qed.

  (* The ctrl_finish call (0x84d24 .. 0x84d30): stamps the block, then the em_fr trailer via atail3_on. *)
  Lemma atail2_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25
                        u3 u4 u5 u6 : word) (mc mbz : word -> option byte) (jf : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) [CB 24 jf; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
                                    C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -128) ->
    munch aWL mbz mc ->
    wmono rsegs mbz mc -> mem_inv rsegs mc -> aJ_on mc ->
    bytes_at rsegs mc f row -> addressable mc (f + 18) 3 ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] ->
    rw_cells rsegs mc (o + 12) [CB 6 HDR] -> rw_cells rsegs mc (o + 18) [CB 32 LB] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG (aQg_on mbz aWL)
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
      - rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - intros _; rewrite Esp; unfold CTRL_FINISH_FRAME; lia.
      - exact ACm.
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
    assert (AJm1 : aJ_on m1).
    { apply (aJ_wout_on ((SP0 + -128 - 16, SP0 + -128) :: fin_w CC RO RL o) mc m1 API ART AJ MU1 WM1 SUBw).
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
    eapply (atail3_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mbz jf);
      [ exact HE | exact FRm1 | exact ST1 | exact MUf | exact WMf | exact MIm1 | exact AJm1
      | exact P1' | exact P2' | exact P3' | exact P4' | exact P5' | exact P6' | exact CLS' ].
  Qed.

  (* atail_pre_on: the body 0x84be4 -> 0x84c40 (checked_memset; the row[0]/row[1] loads; the two checked_memcpy),
     ending at the first checked header byte store, handed to the continuation K (atail_k_on, for atail_on below). *)
  Lemma atail_pre_on : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                          (mc : word -> option byte) (jf : list byte)
      (K : forall (y1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (m2 : word -> option byte),
        aJ_on m2 ->
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
        evtF rsegs RNG aMid_on
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
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    evtF rsegs RNG aMid_on
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
    pose proof HMS_on as HMm. unfold asan_memset_cF_on.asan_memset_contract_F_on, ASAN_MEMSET_K in HMm.
    cbv zeta in HMm.
    eapply evtF_cut.
    { eapply HMm with (RNG := RNG) (junk := junk) (lo := LO); rewrite ?Esp, ?Eo, ?ELEN;
      first
        [ exact HOc | exact AOm | exact ART | exact ST | exact HHM | exact ACm | exact MI
        | exact (A.ShadowRwOn.shadow_rw_on_mono Rsh _ _ (aR_set HE _ _ Eo ELEN) SWm)
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
    assert (AJ1 : aJ_on m1).
    { apply (aJ_wout_on [(o, o + LEN); (SP0 + -128 - 2208, SP0 + -128)] mc m1 API ART AJ MU1 WM1 SUBw1).
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
    pose proof HMC_on as HMc1. unfold asan_memcpy_cF_on.asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMc1.
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
      | exact (A.ShadowRwOn.shadow_rw_on_mono Rsh _ _
                 (aR_cpy HE _ _ _ o d Eo Ed E6 ltac:(lia) ltac:(lia) (or_introl eq_refl)) SW1x)
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
    assert (AJ2 : aJ_on m2).
    { apply (aJ_wout_on [(o, o + 6); (SP0 + -128 - 2224, SP0 + -128)] m1 m2 API ART AJ1 MU2 WM2 SUBw2).
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
    pose proof HMC_on as HMc2. unfold asan_memcpy_cF_on.asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMc2.
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
      | exact (A.ShadowRwOn.shadow_rw_on_mono Rsh _ _
                 (aR_cpy HE _ _ _ (o + 6) s Eo6 Es E6 ltac:(lia) ltac:(lia) (or_intror eq_refl)) SW2x)
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

  (* ---- atail_on: the body 0x84be4 -> aMid_on. atail_pre_on runs 0x84be4 -> 0x84c40; atail_k_on proves its continuation:
     the six checked header byte stores (0x84c40 .. 0x84cdc), then alay_pre_on: the four argument moves of the
     ctrl_lay_block call.  The frame at SP0 + -128 holds P at +8 and ns at +16 (stored before 0x84be4); the
     reac_braid_encode call (in the second stretch) loads its a2 and a4 from there. ---- *)
  (* The state carried through the six header stores: the header cells h at o + 12. *)
  Definition aH_on (jf : list byte) (mc : word -> option byte) (h : list cell) : Prop :=
    aJ_on mc /\ stk rsegs mc LO (SP0 + -128) /\ munch aWL m mc /\ wmono rsegs m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (SP0 + -128) (CB 24 jf :: aFT) /\
    rw_cells rsegs mc o [CB 6 db] /\ rw_cells rsegs mc (o + 6) [CB 6 sb] /\ rw_cells rsegs mc (o + 12) h /\
    rw_cells rsegs mc (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] /\
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] /\
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)].

  Lemma aH_ao_on : forall jf mc h, aH_on jf mc h -> addressable mc o LEN.
  Proof. intros jf mc h (AJ & _). destruct AJ as (_ & _ & _ & AO' & _). exact AO'. Qed.

  Lemma aH_ok_on : forall jf mc h k c a, aH_on jf mc h -> cell_at h k = Some c -> csize c = 1%nat ->
    a = o + 12 + Z.of_nat k -> store_ok rsegs mc (Z_to_bv 64 a) 1 = true.
  Proof.
    intros jf mc h k c a (_ & _ & _ & _ & _ & _ & _ & _ & P3 & _) Hcl Hs ->.
    exact (rw_cells_store_ok rsegs mc (o + 12) h k c 1 P3 Hcl (eq_sym Hs)).
  Qed.

  (* One checked header byte store at o + 12 + k. *)
  Lemma aH_st_on : forall jf mc h k c a (b : byte), EE = true -> aH_on jf mc h -> cells_size h = 6%nat ->
    cell_at h k = Some c -> csize c = 1%nat -> a = o + 12 + Z.of_nat k ->
    aH_on jf (write_to_mem mc (Z_to_bv 64 a) [b]) (cell_upd h k (C1 b)).
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
    unfold aH_on.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
    - apply (aJ_ostore_on mc _ b AJ API ART). lia.
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

  (* After the sb of a header byte: the next aH_on, in the memory named afresh. *)
  Ltac a_hstore HE AH k :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?A) [?bb]) _) =>
        let AH' := fresh "AH" in
        pose proof (aH_st_on _ mm _ k (C1 (Z_to_bv 8 0)) A bb HE AH eq_refl eq_refl eq_refl ltac:(lia)) as AH';
        cbn [cell_upd csize Nat.eqb Nat.sub] in AH';
        let m' := fresh "m" in
        set (m' := write_to_mem mm (Z_to_bv 64 A) [bb]) in *; clearbody m'; clear AH; rename AH' into AH
    end.

  (* 0x84cdc .. 0x84cec, the end of the first stretch: the four argument moves a0 = o (s4), a1 = f (s3),
     a2 = md (s6), a3 = g (s8), and then the state the `jal` at 0x84cec hands to ctrl_lay_block.  This is the
     cut: the facts this run carries (aJ_on, the frame, the output cells) travel in aAtLay_on, and the call itself is
     not taken here. *)
  Lemma alay_pre_on : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                      (mc : word -> option byte) (j0 : list byte) (P : word),
    EE = true -> length j0 = 8%nat ->
    aJ_on mc -> stk rsegs mc LO (SP0 + -128) -> munch aWL m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    rw_cells rsegs mc o [CB 6 db] -> rw_cells rsegs mc (o + 6) [CB 6 sb] -> rw_cells rsegs mc (o + 12) [CB 6 HDR] ->
    rw_cells rsegs mc (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
    rw_cells rsegs mc (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs mc (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG aMid_on
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

  (* ---- THE SECOND STRETCH, the return point 0x84cf0 -> ret, RE-BASED on the return memory m5.
     0x84cf0 .. 0x84d24: the check of row[23] (at f + 23) and its load; the frame word ns at SP0 + -112; when
     row[23] <> 0, the reac_braid_encode call (0x84d20) with a2 = P, a4 = ns; then atail2_on (the ctrl_finish call
     at 0x84d2c and the trailer), and the epilogue.
     EVERY premise is a fact AT m5, the memory ctrl_lay_block returns: no munch, no wmono and no cell of the
     memory before the call.  The core's astack_malloc_realizes gives only VIEW facts across that call
     (a Theorem Labs lane on lib/Reusable/YG0d.v:285-300), so a caller in cgif form can supply facts at m5 but cannot
     relate the two memories as raw memories.
     The conclusion is this stretch's OWN post aQg_on m5 aWL: the run writes only
     inside [LO, SP0) and the output [o, o + LEN), and allocates no fake-stack frame, so neither an
     fp_w [0; 1] FS range nor the stack-shadow range is in its window.  The glue turns it into the whole
     function's post for a caller that holds the cumulative munch / wmono from m. ---- *)
  Lemma ctrl_emit_as_post_lay_F_on :
    forall (x1 c0 c1 c2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 : word)
           (m5 : word -> option byte) (j0 : list byte) (P : word),
    EE = true -> length j0 = 8%nat ->
    (* the state of the run at the return point, every fact AT m5 *)
    aJ_on m5 -> stk rsegs m5 LO (SP0 + -128) ->
    mem_inv rsegs m5 ->
    rw_cells rsegs m5 (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    bytes_at rsegs m5 f row -> addressable m5 f 24 ->
    rw_cells rsegs m5 o [CB 6 db] -> rw_cells rsegs m5 (o + 6) [CB 6 sb] ->
    rw_cells rsegs m5 (o + 12) [CB 6 HDR] -> rw_cells rsegs m5 (o + 18) [CB 32 LB] ->
    rw_cells rsegs m5 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
    rw_cells rsegs m5 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
    evtF rsegs RNG (aQg_on m5 aWL)
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
    - eapply (atail2_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 m5
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
      pose proof (aJ_win_on _ m5 m6 AJ5 MU6 WM6 SUB6) as AJ6.
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
      eapply (atail2_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 m5
                (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)));
        [ exact HE | apply afr_merge; exact FR6 | exact ST6' | exact MUb6 | exact WM6
        | exact MI6' | exact AJ6
        | exact HR6 | exact (addressable_sub m6 f 24 18 3 ADf6 ltac:(lia) ltac:(lia) ltac:(lia))
        | exact P1'' | exact P2'' | exact P3'' | exact P4'' | exact P5'' | exact P6'' ].
  Qed.

  (* The continuation of atail_pre_on at 0x84c40: the six checked header byte stores (136, 25, the two bytes of a5,
     row[0], row[1] at o + 12 .. o + 17), then alay_pre_on. *)
  Lemma atail_k_on : forall (j0 : list byte) (P : word), length j0 = 8%nat -> EE = true ->
    forall (y1 w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word) (m2 : word -> option byte),
      aJ_on m2 -> stk rsegs m2 LO (SP0 + -128) -> munch aWL m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      rw_cells rsegs m2 (SP0 + -128) (CB 24 (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) :: aFT) ->
      bytes_at rsegs m2 f row -> addressable m2 f 24 ->
      rw_cells rsegs m2 o [CB 6 db] -> rw_cells rsegs m2 (o + 6) [CB 6 sb] ->
      rw_cells rsegs m2 (o + 12) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
      rw_cells rsegs m2 (o + 18) [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
      rw_cells rsegs m2 (o + 50) [CB (Z.to_nat (LEN - 52)) (repeat (Z_to_bv 8 0) (Z.to_nat (LEN - 52)))] ->
      rw_cells rsegs m2 (o + LEN + -2) [CB 2 (repeat (Z_to_bv 8 0) 2)] ->
      evtF rsegs RNG aMid_on
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
    change (aH_on (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) m2
              [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
               C1 (Z_to_bv 8 0)]) in AH.
    clear AJ ST MU WM MI FR P1 P2 P3 P4 P5 P6.
    (* addi a0,s4,12; the check of o + 12; li a1,136; addi a0,s4,13; sb a1,12(s4) *)
    step.
    chk_go (o + 12) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 12) 12 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 0 (C1 (Z_to_bv 8 0)) (o + 12) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 0%nat. clear HS.
    (* the check of o + 13; li a1,25; addi a0,s4,14; sb a1,13(s4) *)
    chk_go (o + 13) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 13) 13 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 1 (C1 (Z_to_bv 8 0)) (o + 13) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 1%nat. clear HS.
    (* the check of o + 14; sb s5,14(s4); addi a0,s4,15 *)
    chk_go (o + 14) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 14) 14 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 2 (C1 (Z_to_bv 8 0)) (o + 14) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 2%nat. clear HS.
    step.
    (* the check of o + 15; srli a1,s5,8; addi a0,s4,16; sb a1,15(s4) *)
    chk_go (o + 15) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 15) 15 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 3 (C1 (Z_to_bv 8 0)) (o + 15) AH eq_refl eq_refl ltac:(lia)) as HS.
    do 3 step. a_hstore HE AH 3%nat. clear HS.
    (* the check of o + 16; sb s1,16(s4); addi a0,s4,17 *)
    chk_go (o + 16) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 16) 16 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 4 (C1 (Z_to_bv 8 0)) (o + 16) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 4%nat. clear HS.
    step.
    (* the check of o + 17; sb s0,17(s4) *)
    chk_go (o + 17) (Z_to_bv 5 12) (a_shadow _ o LEN (o + 17) 17 (aH_ao_on _ _ _ AH) ltac:(lia) ltac:(lia)) no_extra.
    pose proof (aH_ok_on _ _ _ 5 (C1 (Z_to_bv 8 0)) (o + 17) AH eq_refl eq_refl ltac:(lia)) as HS.
    step. a_hstore HE AH 5%nat. clear HS.
    destruct AH as (AJh & STh & MUh & WMh & MIh & FRh & P1h & P2h & P3h & P4h & P5h & P6h).
    apply em_merge in P3h. cbn [cells_size csize cells_bytes cbytes app Nat.add] in P3h.
    rewrite (em_byte_lit 136), (em_byte_lit 25), em_c16_hi, (em_c16_lo a5), !em_byte_zxb in P3h by lia.
    pose proof (afr_split _ _ _ _ _ _ Lj0 FRh) as FRs.
    eapply alay_pre_on; [ exact HE | exact Lj0 | exact AJh | exact STh | exact MUh | exact WMh | exact MIh | exact FRs
                 | exact P1h | exact P2h | exact P3h | exact P4h | exact P5h | exact P6h ].
  Qed.

  (* atail_on: 0x84be4 -> aMid_on, with the frame word P at SP0 + -120 and ns at SP0 + -112. *)
  Lemma atail_on : forall (x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 : word)
                       (mc : word -> option byte) (j0 : list byte) (P : word),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 8 j0 :: C8 P :: C8 (Z_to_bv 64 ns) :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> aJ_on mc ->
    evtF rsegs RNG aMid_on
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -128)) gp tp u0 u1 u2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 o) a5 (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 g)
               (Z_to_bv 64 s) (Z_to_bv 64 LEN) (Z_to_bv 64 ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x84be4) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc j0 P HE FR ST MU WM MI AJ.
    assert (Lj0 : length j0 = 8%nat) by (destruct FR as [[Hwf _] _]; exact (proj1 Hwf)).
    exact (atail_pre_on x1 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 mc
             (j0 ++ le8 P ++ le8 (Z_to_bv 64 ns)) (atail_k_on j0 P Lj0 HE) HE
             (afr_merge mc _ j0 P (Z_to_bv 64 ns) _ FR) ST MU WM MI AJ).
  Qed.

  (* ---- The front branches, from the end of the prologue (0x84a2c) to atail_on (0x84be4) or to the early return
     aepi0_on (EE = false). Nothing is stored before 0x84ba8, so the frame at SP0 + -128 stays the prologue's
     CB 24 j :: aFT until agate2_on stores P (t3) at +8 and ns (t4) at +16. ---- *)

  (* The runtime state aJ_on of the entry memory, in the EE = true regime. *)
  Lemma aJ0_on : EE = true -> aJ_on m.
  Proof.
    intros HE. pose proof FP as FP'. rewrite HE in FP'.
    split; [exact HAC | split; [exact HSW_on | split; [exact AWIN | split; [exact (proj1 (AO HE)) |
      split; [exact FP' | exact FPT]]]]].
  Qed.

  (* The extra step of the check of a 4-byte load: addi r,r,3 after the andi. *)
  Ltac add3 X := step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia).

  (* agate2_on (0x84b84 .. 0x84be4): a2 = 0 (md <> 0, so the catalogue load is skipped), the stores of P (t3) at
     SP0 + -120 and ns (t4) at SP0 + -112, s5 = a5, s9 = s and s10 = LEN (1492 when row[21] = 2, else
     36 n + 52); then atail_on. *)
  Lemma agate2_on : forall (x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                        (j : list byte),
    EE = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid_on
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
    pose proof (aJ_win_on [(LO, SP0)] m _ (aJ0_on HE) MU WM (ain_sub LO ltac:(lia))) as AJ.
    rewrite (rc_u8_eqb row 21 1) by lia.
    destruct (Z.eqb_spec (rc_u8 row 21) 1) as [L1|L1]; cbv iota.
    - (* row[21] = 1: mv s5,a5; mv s9,a4; li a1,36; mul a0,a0,a1; addi s10,a0,52 *)
      assert (L2 : LL <> 2) by (unfold ubat; unfold rc_u8 in L1; lia).
      do 5 step.
      rewrite (em_len_word n (em_E_wok _ _ _ _ HE L2)).
      replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
        by (unfold em_len; replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact L2);
            reflexivity).
      eapply atail_on; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
    - (* li a0,2; bne a1,a0 *)
      step. step. rewrite (rc_u8_eqb row 21 2) by lia.
      destruct (Z.eqb_spec (rc_u8 row 21) 2) as [L2|L2]; cbn [negb]; cbv iota.
      + (* row[21] = 2: mv s5,a5; mv s9,a4; li s10,1492; j *)
        change (rc_u8 row 21) with (ubat row 21) in L2.
        do 4 step.
        replace (Z_to_bv 64 1492) with (Z_to_bv 64 LEN) by (unfold em_len; rewrite L2; reflexivity).
        eapply atail_on; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
      + (* row[21] = 0: mv a0,s2, then as row[21] = 1 *)
        change (rc_u8 row 21) with (ubat row 21) in L2.
        do 6 step.
        rewrite (em_len_word n (em_E_wok _ _ _ _ HE L2)).
        replace (Z_to_bv 64 (52 + 36 * n)) with (Z_to_bv 64 LEN)
          by (unfold em_len; replace (ubat row 21 =? 2) with false by (symmetry; apply Z.eqb_neq; exact L2);
              reflexivity).
        eapply atail_on; [exact HE | exact FR | exact ST | exact MU | exact WM | exact MI | exact AJ].
  Qed.

  (* agate_on (0x84b48 .. 0x84b84): the check of f + 22 and the load of row[22]; when row[22] = 1, the check of the
     4-byte load at md + 56 and the load of em_hid mb, with the early return (s10 = 0) when it is 0; then
     agate2_on. *)
  Lemma agate_on : forall (x1 u0 u1 u2 x10 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                       (j : list byte),
    LL = 2 \/ em_wok n = true ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid_on
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
        apply amid_q_on.
        eapply aepi0_on; [apply em_E_false_g; assumption | eassumption ..].
      + eapply agate2_on; [apply em_E_true; [exact WL | right; exact H0] | eassumption ..].
    - eapply agate2_on; [apply em_E_true; [exact WL | left; exact G1] | eassumption ..].
  Qed.

  (* achk2_on (0x84a7c .. 0x84b48), row[21] <> 2: the n test (2 <= n <= 40 and n even, else the early return with
     s10 = 0), md <> 0 and a2 = 0; then agate_on. *)
  Lemma achk2_on : forall (x1 u0 u1 u2 x10 x12 x13 x16 x17 x21 x25 x26 P u5 u6 : word) (mc : word -> option byte)
                       (j : list byte),
    LL <> 2 ->
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid_on
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
        eapply agate_on; [right | eassumption ..].
        unfold em_wok. rewrite Ev. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia).
        replace (n <=? 40) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + apply amid_q_on.
        eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]
                      | eassumption ..].
    - apply amid_q_on.
      eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
        by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
    - apply amid_q_on.
      eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
    - apply amid_q_on.
      eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
        by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
  Qed.

  (* afront_on (0x84a2c .. ), the first instruction after the prologue: s3 = f, the check of f + 21 (s4 = o before the
     branch) and the load of row[21]. row[21] = 2: md <> 0, a2 = 0, agate_on. row[21] = 0: the n test (the early
     return with s10 = 0), then md <> 0 and achk2_on. row[21] = 1: md <> 0 and achk2_on. *)
  Lemma afront_on : forall (x1 u0 u1 u2 x12 x13 x16 x17 x19 x20 x21 x25 x26 P u5 u6 : word)
                        (mc : word -> option byte) (j : list byte),
    rw_cells rsegs mc (SP0 + -128) (CB 24 j :: aFT) ->
    stk rsegs mc LO (SP0 + -128) ->
    munch [(LO, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aMid_on
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
      eapply agate_on; [left; exact L2 | eassumption ..].
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
             eapply achk2_on; [exact L2 | eassumption ..].
          -- apply amid_q_on.
             eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; rewrite Ev; apply andb_false_r]
                           | eassumption ..].
        * apply amid_q_on.
          eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (n <=? 40) with false
            by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r; reflexivity] | eassumption ..].
        * apply amid_q_on.
          eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
        * apply amid_q_on.
          eapply aepi0_on; [apply em_E_false_w; [exact L2 | unfold em_wok; replace (2 <=? n) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity] | eassumption ..].
      + (* row[21] = 1: bnez s6 (md <> 0) *)
        step. rewrite rc_eqb by lia.
        replace (md =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmd0). cbn [negb]; cbv iota.
        eapply achk2_on; [exact L2 | eassumption ..].
  Qed.

  (* ---- THE FIRST STRETCH, 0x849d8 -> the ctrl_lay_block call site 0x84cec (aMid_on).
     amain (0x849d8 .. 0x84a2c), the prologue: the 128-byte frame with the 13 saves [CB 24 j; s11 .. s0; ra] at
     SP0 + -128, the moves s8 = g, s2 = n, s7 = d, s6 = md, and the shadow offset s11 = ASAN_K from the runtime's
     cell (the GOT word at 0x9fad0 holds the cell's address 0xa8878); then afront_on.  The run ends either at the
     call site (aAtLay_on) or, when EE = false, at the early return, which the glue widens to the whole post. *)
  Lemma ctrl_emit_as_pre_lay_F_on : forall (t0 t1 t2 t3 t5 t6 : word),
    evtF rsegs RNG aMid_on
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
    (* afront_on as a local fact; the store steps transport (and replace) every stk, bytes_at and mem_inv fact about
       m, so the Section's own facts about m leave the context first *)
    pose proof afront_on as AF. clear HST HR HM HD HSb MI0.
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

End EmitOn.

(* The two stretches rest on nothing but the semantics' own axioms (the build log shows the list). *)
Print Assumptions ctrl_emit_as_pre_lay_F_on.
Print Assumptions ctrl_emit_as_post_lay_F_on.
