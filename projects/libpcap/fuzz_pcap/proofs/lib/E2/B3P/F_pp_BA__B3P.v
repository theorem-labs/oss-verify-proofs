(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_pp_CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_pp_BA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
Local Ltac kt_data e := lazymatch e with context [get_le32 _ _] => idtac | context [get_le16 _ _] => idtac | context [get_u8 _ _] => idtac end.
Local Ltac kt_big e := lazymatch e with Z.lor _ _ => kt_data e | Z.land _ _ => kt_data e | Z.shiftl _ _ => kt_data e | Z.shiftr _ _ => kt_data e | Z.modulo _ _ => kt_data e end.
Local Ltac kill_towers := repeat (lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
  match R with context [Z_to_bv _ ?e] => kt_big e; let v := fresh "kv" in generalize (Z_to_bv 64 e) as v; intro v end end).
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (562600%Z, 562600%Z) => idtac | (562600%Z, 564948%Z) => idtac | (562740%Z, 562740%Z) => idtac | (562740%Z, 564820%Z) => idtac | (562764%Z, 562764%Z) => idtac | (562764%Z, 564832%Z) => idtac | (562836%Z, 562836%Z) => idtac | (562836%Z, 564964%Z) => idtac | (563032%Z, 563032%Z) => idtac | (563032%Z, 564884%Z) => idtac | (563044%Z, 563044%Z) => idtac | (563044%Z, 564900%Z) => idtac | (563132%Z, 563132%Z) => idtac | (563132%Z, 564916%Z) => idtac | (563144%Z, 563144%Z) => idtac | (563144%Z, 564932%Z) => idtac | (563232%Z, 563232%Z) => idtac | (563232%Z, 564992%Z) => idtac | (563244%Z, 563244%Z) => idtac | (563244%Z, 565008%Z) => idtac | (563332%Z, 563332%Z) => idtac | (563332%Z, 565100%Z) => idtac | (564144%Z, 564144%Z) => idtac | (564144%Z, 565056%Z) => idtac | (564156%Z, 564156%Z) => idtac | (564156%Z, 565072%Z) => idtac | (564236%Z, 564236%Z) => idtac | (564236%Z, 565148%Z) => idtac | (564248%Z, 564248%Z) => idtac | (564248%Z, 565164%Z) => idtac | (564296%Z, 564296%Z) => idtac | (564296%Z, 565248%Z) => idtac | (564360%Z, 564360%Z) => idtac | (564360%Z, 565024%Z) => idtac | (564372%Z, 564372%Z) => idtac | (564372%Z, 565040%Z) => idtac | (564452%Z, 564452%Z) => idtac | (564452%Z, 565116%Z) => idtac | (564464%Z, 564464%Z) => idtac | (564464%Z, 565132%Z) => idtac | (564512%Z, 564512%Z) => idtac | (564512%Z, 565216%Z) => idtac | (564524%Z, 562612%Z) => idtac | (564524%Z, 562848%Z) => idtac | (564524%Z, 563344%Z) => idtac | (564524%Z, 564308%Z) => idtac | (564524%Z, 564524%Z) => idtac | (564524%Z, 565232%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Ltac rf_norm' := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_pflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x896d4) (c_fc c) None m (seg_rom asegs)).
Section Sz1.
Variables c : ltac2:(SecDiet.SzSec.tyM 'pflog_spec__stmt "v" @c).
#[using="Type"] Lemma pflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pp_init WF I.
  unfold swap_pflog_header. cbn [h_caplen h_len].
  bd_F. lstep. bd_F.
  zstep. ck0 UNPH; ck_go.
  zstep. ck0 UNPH. do 3 zstep. lstep. ck_go.
  rewrite sx32_small by lia.
  lstep. gsplit_TF (c_caplen c) 48%Z.
  lstep. gsplit_TF (c_len0 c) 48%Z.
  bd_F. lstep. bd_F.
  ck0 UNPD; ck_go.
  rd1 0%Z. lstep. gsplit_TF constr:(get_u8 d 0) 48%Z.
  zstep. ckp_at UNPD (c_DA c + 44)%Z 4%Z. do 3 zstep. ck_cut 0x89758%Z [17%Z]. zstep. rd4 44%Z. ck_cut 0x89764%Z [17%Z]. ckp_clear.
  do 12 lstep. st4 44%Z. kill_towers.
  gsplit_TF (c_caplen c) 52%Z. gsplit_TF (c_len0 c) 52%Z. lstep. gsplit_TF constr:(get_u8 d 0) 52%Z.
  zstep. ckp_at UNPD (c_DA c + 48)%Z 4%Z. do 3 zstep. ck_cut 0x897bc%Z [17%Z]. zstep. rd4 48%Z. ck_cut 0x897c8%Z [17%Z]. ckp_clear.
  do 12 lstep. st4 48%Z. kill_towers.
  gsplit_TF (c_caplen c) 56%Z. gsplit_TF (c_len0 c) 56%Z. lstep. gsplit_TF constr:(get_u8 d 0) 56%Z.
  zstep. ckp_at UNPD (c_DA c + 52)%Z 4%Z. do 3 zstep. ck_cut 0x89820%Z [17%Z]. zstep. rd4 52%Z. ck_cut 0x8982c%Z [17%Z]. ckp_clear.
  do 12 lstep. st4 52%Z. kill_towers.
  gsplit_TF (c_caplen c) 60%Z. gsplit_TF (c_len0 c) 60%Z. lstep. gsplit_TF constr:(get_u8 d 0) 60%Z.
  zstep. ckp_at UNPD (c_DA c + 56)%Z 4%Z. do 3 zstep. ck_cut 0x89884%Z [12%Z]. zstep. rd4 56%Z. ck_cut 0x89d2c%Z [13%Z]. ckp_clear.
  do 11 lstep. st4 56%Z. kill_towers.
  epilog.
Qed.
End Sz1.
#[using="Type"] Lemma pflog_spec : ltac:(let t := eval cbv delta [pflog_spec__stmt] in pflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'pflog_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll2_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_linux_sll2_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x894e4) (c_fc c) None m (seg_rom asegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll2_spec__stmt "v" @c).
#[using="Type"] Lemma sll2_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll2_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pp_init WF I.
  unfold swap_linux_sll2_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  bd_F. lstep. bd_F.
  zstep. ck0 UNPH; ck_go.
  zstep. ck0 UNPH. do 3 zstep. lstep. ck_go.
  rewrite sx32_small by lia.
  lstep. gsplit_TF (c_caplen c) 20%Z.
  lstep. gsplit_TF (c_len0 c) 20%Z.
  bd_F. lstep. bd_F. lstep. bd_F.
  ck0 UNPD; ck_go.
  zstep. ck0 UNPD. do 3 zstep. rd1 0%Z. ck_go.
  rd1 1%Z.
  do 7 lstep.
  lstep.
  rewrite lor_be16 by lia. unfold get_be16. replace (0 + 1)%Z with 1%Z by reflexivity.
  rewrite swrap_of_sx32 by lia. rewrite (swrap32_small (c_caplen c + -20)) by lia.
  set (p := (get_u8 d 0 * 256 + get_u8 d 1)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - lstep. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    ckp_at UNPD (c_DA c + 20)%Z 4%Z. do 3 zstep. ck_cut 0x895a8%Z [12%Z]. zstep. rd4 20%Z. ck_cut 0x89d2c%Z [13%Z]. ckp_clear.
    do 11 lstep. st4 20%Z. kill_towers. epilog.
  - lstep. esplit_FT p 14%Z. 2:{ epilog. }
    lstep. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    ckp_at UNPD (c_DA c + 20)%Z 4%Z. do 3 zstep. ck_cut 0x89c88%Z [16%Z]. zstep. rd4 20%Z. ck_cut 0x89c94%Z [16%Z]. ckp_clear.
    do 12 lstep. st4 20%Z. kill_towers.
    gsplit_TF (c_caplen c - 20)%Z 8%Z. gsplit_TF (c_len0 c - 20)%Z 8%Z.
    zstep. ckp_at UNPD (c_DA c + 26)%Z 2%Z. do 3 zstep. ck_cut 0x89ce4%Z [16%Z]. zstep. rd2 26%Z. ck_cut 0x89cf0%Z [16%Z]. ckp_clear.
    do 4 lstep. st2 26%Z. kill_towers.
    gsplit_TF (c_caplen c - 20)%Z 12%Z. gsplit_TF (c_len0 c - 20)%Z 12%Z.
    zstep. ckp_at UNPD (c_DA c + 28)%Z 4%Z. do 3 zstep. ck_cut 0x89d20%Z [12%Z]. zstep. rd4 28%Z. ck_cut 0x89d2c%Z [13%Z]. ckp_clear.
    do 11 lstep. st4 28%Z. kill_towers. epilog.
Qed.
End Sz2.
#[using="Type"] Lemma sll2_spec : ltac:(let t := eval cbv delta [sll2_spec__stmt] in sll2_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'sll2_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_linux_sll_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x895c4) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll_spec__stmt "v" @c).
#[using="Type"] Lemma sll_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pp_init WF I.
  unfold swap_linux_sll_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  bd_F. lstep. bd_F.
  zstep. ck0 UNPH; ck_go.
  zstep. ck0 UNPH. do 3 zstep. lstep. ck_go.
  rewrite sx32_small by lia.
  lstep. gsplit_TF (c_caplen c) 16%Z.
  lstep. gsplit_TF (c_len0 c) 16%Z.
  bd_F. lstep. bd_F. lstep. bd_F.
  zstep. ckp_at UNPD (c_DA c + 14)%Z 1%Z. do 3 zstep. ck_cut 0x89634%Z [15%Z]. ckp_clear.
  zstep. ckp_at UNPD (c_DA c + 15)%Z 1%Z. do 3 zstep. rd1 14%Z. ck_cut 0x8964c%Z [16%Z]. ckp_clear.
  rd1 15%Z.
  do 7 lstep. lstep.
  rewrite lor_be16 by lia. unfold get_be16. replace (14 + 1)%Z with 15%Z by reflexivity.
  rewrite swrap_of_sx32 by lia. rewrite (swrap32_small (c_caplen c + -16)) by lia.
  set (p := (get_u8 d 14 * 256 + get_u8 d 15)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - lstep. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z.
    lstep. bd_F.
    ckp_at UNPD (c_DA c + 16)%Z 4%Z. do 3 zstep. ck_cut 0x89694%Z [12%Z]. zstep. rd4 16%Z. ck_cut 0x89d2c%Z [13%Z]. ckp_clear.
    do 11 lstep. st4 16%Z. kill_towers. epilog.
  - lstep. esplit_FT p 14%Z. 2:{ epilog. }
    lstep. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z.
    lstep. bd_F.
    ckp_at UNPD (c_DA c + 16)%Z 4%Z. do 3 zstep. ck_cut 0x89bb0%Z [16%Z]. zstep. rd4 16%Z. ck_cut 0x89bbc%Z [16%Z]. ckp_clear.
    do 12 lstep. st4 16%Z. kill_towers.
    gsplit_TF (c_caplen c - 16)%Z 8%Z. gsplit_TF (c_len0 c - 16)%Z 8%Z.
    zstep. ckp_at UNPD (c_DA c + 22)%Z 2%Z. do 3 zstep. ck_cut 0x89c0c%Z [16%Z]. zstep. rd2 22%Z. ck_cut 0x89c18%Z [16%Z]. ckp_clear.
    do 4 lstep. st2 22%Z. kill_towers.
    gsplit_TF (c_caplen c - 16)%Z 12%Z. gsplit_TF (c_len0 c - 16)%Z 12%Z.
    zstep. ckp_at UNPD (c_DA c + 24)%Z 4%Z. do 3 zstep. ck_cut 0x89c48%Z [12%Z]. zstep. rd4 24%Z. ck_cut 0x89d2c%Z [13%Z]. ckp_clear.
    do 11 lstep. st4 24%Z. kill_towers. epilog.
Qed.
End Sz3.
#[using="Type"] Lemma sll_spec : ltac:(let t := eval cbv delta [sll_spec__stmt] in sll_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'sll_spec__body "v"). Qed.
End CANSEC1.
End F_pp_BA.

(* [comment removed for export] *)
Module F_pp_EA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.


(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma swap_nflog_tlvs_S : forall f cap len p d,
  swap_nflog_tlvs (S f) cap len p d =
  (if cap <? 4 then d else
  let d2 := swap_field 2 p (swap_field 2 (p + 2) d) in
  let size := get_le16 d2 p in
  let size' := if size mod 4 =? 0 then size else size + (4 - size mod 4) in
  if size' <? 4 then d2 else if (cap <? size') || (len <? size') then d2
  else swap_nflog_tlvs f (cap - size') (len - size') (p + size') d2)%Z.
Proof. reflexivity. Qed.
Lemma swap_nflog_tlvs_exit : forall f cap len p d, (cap < 4)%Z -> swap_nflog_tlvs f cap len p d = d.
Proof. intros [|f] cap len p d H; [reflexivity|]. rewrite swap_nflog_tlvs_S. replace (cap <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
(* [comment removed for export] *)
Ltac nf_exit := run; bdecide; epilog.
Local Ltac nf_exit__c1 := run; bd_T; epilog.
Local Ltac nf_exit__c2 := run; bd_T; epilog.
Local Ltac nf_exit__c3 := run; bd_T; epilog.
Local Ltac nf_exit__c4 := run; bd_T; epilog.

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (563464%Z, 563464%Z) => idtac | (563464%Z, 564804%Z) => idtac | (563540%Z, 563540%Z) => idtac | (563540%Z, 563680%Z) => idtac | (563552%Z, 563552%Z) => idtac | (563552%Z, 563696%Z) => idtac | (563584%Z, 563584%Z) => idtac | (563584%Z, 563712%Z) => idtac | (563596%Z, 563596%Z) => idtac | (563596%Z, 563728%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
Section CANSEC1. Context {rc : runConstT}.

Definition nflog_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (capc lenc p : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  (4 * Z.of_nat f >= capc + 4)%Z -> (4 <= capc)%Z -> (p + capc = c_caplen c)%Z -> (4 <= p)%Z -> (p mod 4 = 0)%Z -> (0 <= lenc < 2^32)%Z ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  a1 = Z_to_bv 64 (c_DA c + p) -> a5 = Z_to_bv 64 capc -> a7 = Z_to_bv 64 (bv_swrap 32 lenc) ->
  a6 = Z_to_bv 64 4 -> t0 = Z_to_bv 64 65532 -> t1 = Z_to_bv 64 3 ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_nflog_tlvs f capc lenc p d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x89938) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_loop__stmt "vhk" @c).
#[using="Type"] Lemma nflog_loop__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_loop__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros capc lenc p; intros until d; intros I FU C4p PC P4 PM LR -> -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. pp_init WF I.
  rewrite swap_nflog_tlvs_S. replace (capc <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta. simpl_if.
  set (d2 := swap_field 2 p (swap_field 2 (p + 2) d)).
  set (size := get_le16 d2 p).
  set (size' := if (size mod 4 =? 0)%Z then size else (size + (4 - size mod 4))%Z).
  lstep. bd_F.
  zstep.
  ckp_at UNPD (c_DA c + p + 2)%Z 2%Z. do 3 zstep. ck_cut 0x89954%Z [29%Z]. zstep. rd2 (p + 2)%Z. ck_cut 0x89960%Z [29%Z]. ckp_clear.
  do 4 lstep.
  st2 (p + 2)%Z.
  ckp_at UNPD (c_DA c + p)%Z 2%Z. do 2 zstep. ck_cut 0x89980%Z [28%Z]. zstep.
  name2 p. rd2 p. ck_cut 0x8998c%Z [28%Z]. ckp_clear.
  do 4 lstep.
  lazymatch goal with EWa : zslice p 2 _ = [?y0; ?y1] |- _ => sh_lanes p [y1; y0] end.
  lazymatch goal with EWa : zslice p 2 ?d1 = [?y0; ?y1], Hd1 : ?d1 = swap_field 2 (p + 2) d |- _ =>
    let E := fresh "E" in
    assert (E : buf_write_at p [y1; y0] d1 = d2)
      by (subst d2; rewrite <- ?Hd1; unfold swap_field; rewrite EWa; reflexivity);
    assert (SZ : size = (y1 + 256 * y0)%Z)
      by (subst size; rewrite <- E; apply get_le16_write_same; lia);
    rewrite E in *; clear E; clearbody d2;
    rewrite (get_le16_of_slice _ _ _ _ EWa); rewrite swap16_val by lia;
    replace size' with (if ((y1 + 256 * y0) mod 4 =? 0)%Z then (y1 + 256 * y0)%Z else (y1 + 256 * y0 + (4 - (y1 + 256 * y0) mod 4))%Z)
      by (subst size' size; rewrite SZ; reflexivity);
    clear size' size SZ;
    set (sw := (y1 + 256 * y0)%Z) in *;
    assert (SW : (0 <= sw < 65536)%Z) by lia;
    rewrite land_3 by lia;
    replace ((sw + 65536 * y1) mod 4)%Z with (sw mod 4)%Z by zlia
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (CONT : forall (t2q t3q t4q : word) (sz : Z), (0 <= sz < 2^32)%Z -> (sz mod 4 = 0)%Z ->
    evtF asegs (c_RNG c) (ppost c (c_len0 c)
                (if sz <? 4 then d2 else if (capc <? sz) || (lenc <? sz) then d2
                 else swap_nflog_tlvs f (capc - sz) (lenc - sz) (p + sz) d2))
      (MS (mkR ra (SPM c) (c_gp c) (c_tp c) (Z_to_bv 64 65532) (Z_to_bv 64 3) t2q s0 s1 (Z_to_bv 64 239)
               (Z_to_bv 64 (c_DA c + p)) (Z_to_bv 64 (c_HA c)) (Z_to_bv 64 (c_DA c)) (Z_to_bv 64 sz) (Z_to_bv 64 capc) (Z_to_bv 64 4) (Z_to_bv 64 (bv_swrap 32 lenc)) SBW
               s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3q t4q t5 t6)
          (c_F c) (Z_to_bv 64 0x899b8) (c_fc c) None mm (seg_rom asegs))) end.
  { intros t2q t3q t4q sz SZR SZM.
    destruct (Z.ltb_spec sz 4) as [S4|S4]. { bd_T. nf_exit__c1. } bd_F.
    destruct (Z.ltb_spec capc sz) as [S5|S5]. { bd_T. cbn [orb]. nf_exit__c2. } bd_F. cbn [orb].
    destruct (Z.ltb_spec lenc sz) as [S6|S6]. { bd_T. nf_exit__c3. } bd_F.
    lstep. bd_F.
    run. rf_norm.
    rewrite (swrap32_small (capc - sz)) by lia.
    destruct (Z.ltb_spec 3 (capc - sz)) as [S7|S7]; cycle 1.
    { bd_F. rewrite swap_nflog_tlvs_exit by lia. nf_exit__c4. }
    bd_T. eapply (IH (capc - sz)%Z (lenc - sz)%Z (p + sz)%Z); fastfirst (first [ noevar_assumption |close_inv | wordeq | lia | zlia]). }
  destruct (Z.eqb_spec (sw mod 4) 0) as [M0|M0]; simpl_if.
  - bd_T. do 2 lstep.
    replace ((sw + 65536 * x3) mod 65536)%Z with sw by zlia.
    eapply (CONT _ _ _ sw); [lia | exact M0].
  - bd_F. lstep. rewrite land_65532 by lia.
    replace ((sw + 65536 * x3) mod 65536 - (sw + 65536 * x3) mod 4)%Z with (sw - sw mod 4)%Z by zlia.
    do 2 lstep.
    replace (sw - sw mod 4 + 4)%Z with (sw + (4 - sw mod 4))%Z by lia.
    eapply (CONT _ _ _ (sw + (4 - sw mod 4))%Z); [zlia | zlia].
Qed.
End Sz3.
#[using="Type"] Lemma nflog_loop : ltac:(let t := eval cbv delta [nflog_loop__stmt] in nflog_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'nflog_loop__body "vhk"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_nflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x898a0) (c_fc c) None m (seg_rom asegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_spec__stmt "v" @c).
#[using="Type"] Lemma nflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> -> ->.
 pose proof WF as WF'. pose proof I as I'. pp_init WF I.
  unfold swap_nflog_header. cbn [h_caplen h_len].
  bd_F. lstep. bd_F.
  zstep. ck0 UNPH; ck_go.
  zstep. ck0 UNPH. do 3 zstep. lstep. ck_go.
  lstep. rewrite sx32_small by lia. gsplit_TF (c_caplen c) 4%Z.
  lstep. gsplit_TF (c_len0 c) 4%Z.
  bd_F. lstep. bd_F.
  zstep. ckp_at UNPD (c_DA c + 1)%Z 1%Z. do 3 zstep. ck_cut 0x89908%Z [16%Z]. ckp_clear.
  rd1 1%Z.
  destruct (Z.eqb_spec (get_u8 d 1) 0) as [V0|V0]; cycle 1.
  { bd_T. cbn [negb]. epilog. }
  bd_F. cbn [negb].
  lstep. bd_F.
  do 2 lstep. rf_norm. rewrite (swrap32_small (c_caplen c + -4)) by lia.
  destruct (Z.ltb_spec (c_caplen c - 4) 4) as [C8'|C8'].
  { bd_T. rewrite swap_nflog_tlvs_exit by lia. epilog. }
  bd_F. do 5 lstep. rf_norm.
  eapply (nflog_loop c WF' (Z.to_nat (c_caplen c / 4 + 1)) (c_caplen c - 4)%Z (c_len0 c - 4)%Z 4%Z); fastfirst (first [ noevar_assumption | exact I' | close_inv | wordeq | lia | zlia | reflexivity]).
Qed.
End Sz4.
#[using="Type"] Lemma nflog_spec : ltac:(let t := eval cbv delta [nflog_spec__stmt] in nflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'nflog_spec__body "v"). Qed.

End CANSEC1.
End F_pp_EA.

(* [comment removed for export] *)
Module F_pp_LA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.


(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma iso_data_len_loop_exit : forall f nd j bl pre d,
  (j <? nd) && (16 <=? bl) = false -> iso_data_len_loop f nd j bl pre d = pre.
Proof. intros [|f] nd j bl pre d H; cbn [iso_data_len_loop]; [reflexivity|]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?Z.add_0_r.
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (565456%Z, 565456%Z) => idtac | (565456%Z, 565720%Z) => idtac | (565536%Z, 565536%Z) => idtac | (565536%Z, 565632%Z) => idtac | (565568%Z, 565568%Z) => idtac | (565568%Z, 565648%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition linv (c : ppctx) (m : mem) (d : list Z) (hlen : Z) (j0 : list byte) (raL : word) : Prop :=
  rw_cells asegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at asegs m (c_DA c) (zbytes d) /\ wr_at asegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv asegs m /\ munch (FOOT c) (c_m0 c) m /\ wmono asegs (c_m0 c) m
  /\ stk asegs m (c_lo c) (bv_unsigned (c_sp c) + -64)
  /\ rw_cells asegs m (bv_unsigned (c_sp c) + -64) [CB 8 j0; C8 raL]
  /\ rw_cells asegs m (bv_unsigned (c_sp c) + -48) [CB 8 (c_junk c); C8 (c_s3 c); C8 (c_s2 c); C8 (c_s1 c); C8 (c_s0 c); C8 (c_ra c)]
  /\ unpoisoned m (c_HA c) (c_HA c + 24) /\ unpoisoned m (c_DA c) (c_DA c + Z.of_nat (c_N c)).

Ltac open_linv I :=
  destruct I as (HDR & ZB & ZW & ZR & LD & MI & MU & WM & ST & FRL & FR & UNPH & UNPD);
  lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d) =>
    let LZ := fresh "LZ" in pose proof (zbytes_length d) as LZ; rewrite LD in LZ end;
  unfold FOOT in MU.
Ltac lp_init WF I :=
  open_wf WF; open_linv I;
  lazymatch goal with |- context [c_sp ?c] =>
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  let AH := fresh "ATOPhi" in pose proof (@ATOP_hi _) as AH.

(* [comment removed for export] *)
Definition leaf_post (c : ppctx) (raL s0 s1 s2 s3 t5 t6 : word) (d : list Z) (hlen : Z) (res : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
    ms' = MS (mkR raL (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_swrap 32 res)) a1 a2 a3 a4 a5 a6 a7 s2
                  s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc raL) (c_fc c) None m' (seg_rom asegs)
    /\ ppinv c m' d hlen.

Notation SPL c := (Z_to_bv 64 (bv_unsigned (c_sp c) + -64)).

Definition leaf_fin__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d hlen j0 raL nd pre,
  linv c m d hlen j0 raL ->
  a2 = Z_to_bv 64 nd -> a4 = Z_to_bv 64 (bv_swrap 32 pre) -> (0 <= nd < 2^32)%Z -> (0 <= pre < 2^32)%Z ->
  evtF asegs (c_RNG c) (leaf_post c raL s0 s1 s2 s3 t5 t6 d hlen (u_int_sum (iso_pseudo_header_len nd) pre))
    (MS (mkR ra (SPL c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a1a0) (c_fc c) None m (seg_rom asegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_fin__stmt "v" @c).
#[using="Type"] Lemma leaf_fin__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_fin__stmt "v").
Proof.
  intros WF; intros until pre; intros I -> -> ND PR.
 lp_init WF I.
  do 6 lstep.
  rewrite !swrap32_add_mod64_l, !swrap32_add_mod64_r. rewrite sat_idiom.
  replace ((Z.shiftl nd 4 mod 18446744073709551616 + 64) mod 2^32)%Z with (iso_pseudo_header_len nd)
    by (unfold iso_pseudo_header_len, u32; rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small pre) by lia.
  do 3 lstep.
  release_frame FRL ST (bv_unsigned (c_sp c) + -48)%Z.
  apply evtF_done. unfold leaf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  unfold ppinv, FOOT. repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Qed.
End Sz2.
#[using="Type"] Lemma leaf_fin : ltac:(let t := eval cbv delta [leaf_fin__stmt] in leaf_fin__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'leaf_fin__body "v"). Qed.

(* [comment removed for export] *)
Definition leaf_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (j pre : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d hlen j0 raL,
  linv c m d hlen j0 raL ->
  let nd := get_le32 d 60 in let bl := (c_caplen c - 64 - 16 * j)%Z in
  (Z.of_nat f >= nd - j)%Z -> (0 <= j < nd)%Z -> (16 <= bl)%Z -> (0 <= pre < 2^32)%Z -> (64 <= c_caplen c)%Z -> (nd <= 128)%Z ->
  t0 = Z_to_bv 64 (c_DA c + (64 + 16 * j)) -> a1 = Z_to_bv 64 (c_DA c + (72 + 16 * j)) -> a6 = Z_to_bv 64 (j + 1) ->
  a2 = Z_to_bv 64 nd -> a3 = SBW -> a4 = Z_to_bv 64 (bv_swrap 32 pre) -> a7 = Z_to_bv 64 15 -> a0 = Z_to_bv 64 (bv_swrap 32 (bl - 16)) ->
  a5 = Z_to_bv 64 (c_DA c + 64) ->
  evtF asegs (c_RNG c) (leaf_post c raL s0 s1 s2 s3 t5 t6 d hlen (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd j bl pre d)))
    (MS (mkR ra (SPL c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a104) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_loop__stmt "vhk" @c).
#[using="Type"] Lemma leaf_loop__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_loop__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros j pre; intros until raL; intros I nd bl FU J BL PR C64 N128 -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof I as I'. pose proof WF as WF'. lp_init WF I.
  assert (ND : (0 <= nd < 2^32)%Z) by (subst nd; apply get_le32_range; exact ZR).
  assert (BLE : bl = (c_caplen c - 64 - 16 * j)%Z) by reflexivity. clearbody bl.
  cbn [iso_data_len_loop].
  replace (j <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (16 <=? bl) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  replace (64 + 16 * j + 8)%Z with (72 + 16 * j)%Z by lia. replace (64 + 16 * j + 4)%Z with (68 + 16 * j)%Z by lia.
  bd_F. (* [comment removed for export] *)
  lstep. zstep.
  ckp_at UNPD (c_DA c + (64 + 16 * j) + 8)%Z 4%Z. do 3 zstep. ck_cut 0x8a120%Z [28%Z]. ckp_clear.
  rd4 (72 + 16 * j)%Z.
  match goal with |- context [iso_data_len_loop f nd (j + 1) (bl - 16) ?p d] => set (pre' := p) end.
  assert (PR' : (0 <= pre' < 2^32)%Z).
  { pose proof (get_le32_range d (68 + 16 * j) ZR). subst pre'. destruct (negb _); [|lia]. destruct (pre <? _); [apply u_int_sum_range; lia | lia]. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (BOT : forall a0q t2q t3q t4q a4q, a4q = Z_to_bv 64 (bv_swrap 32 pre') ->
    evtF asegs (c_RNG c) (leaf_post c raL s0 s1 s2 s3 t5 t6 d hlen (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd (j + 1) (bl - 16) pre' d)))
      (MS (mkR ra (SPL c) (c_gp c) (c_tp c) (Z_to_bv 64 (c_DA c + (64 + 16 * j))) (Z_to_bv 64 (bv_swrap 32 (bl - 16))) t2q s0 s1 a0q (Z_to_bv 64 (c_DA c + (72 + 16 * j))) (Z_to_bv 64 nd)
               SBW a4q (Z_to_bv 64 (c_DA c + 64)) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 15) s2
               s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3q t4q t5 t6)
          (c_F c) (Z_to_bv 64 0x8a164) (c_fc c) None mm (seg_rom asegs))) end.
  { intros a0q t2q t3q t4q a4q ->.
    destruct (Z.ltb_spec (j + 1) nd) as [JN|JN].
    - bd_F. do 4 lstep. rf_norm.
      rewrite (swrap32_small (bl - 16)) by lia.
      destruct (Z.leb_spec 16 (bl - 16)) as [B2|B2].
      + bd_T. replace (bl - 16)%Z with (c_caplen c - 64 - 16 * (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z pre'); fastfirst (first [ noevar_assumption | exact I' | reflexivity | (f_equal; lia) | (do 2 f_equal; lia) | lia
        | (f_equal; rewrite ?swrap32_small by lia; lia) ]).
      + bd_F. lstep. rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        eapply leaf_fin; fastfirst (first [ noevar_assumption | exact WF' | exact I' | reflexivity | lia]).
    - bd_T. rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
      eapply leaf_fin; fastfirst (first [ noevar_assumption | exact WF' | exact I' | reflexivity | lia]). }
  destruct (Z.eqb_spec (get_le32 d (72 + 16 * j)) 0) as [DZ|DZ]; cbn [negb] in pre'.
  - bd_T. subst pre'. eapply BOT. reflexivity.
  - bd_F. bd_F.
    zstep. ckp_at UNPD (c_DA c + (64 + 16 * j) + 4)%Z 4%Z. do 3 zstep. ck_cut 0x8a140%Z [29%Z]. ckp_clear.
    rd4 (68 + 16 * j)%Z.
    do 5 lstep. rf_norm.
    rewrite sat_idiom. rewrite !(Z.mod_small _ (2^32)) by lia.
    set (de := u_int_sum (get_le32 d (68 + 16 * j)) (get_le32 d (72 + 16 * j))) in *.
    assert (DE : (0 <= de < 2^32)%Z) by (subst de; apply u_int_sum_range; lia).
    destruct (Z.ltb_spec pre de) as [LT|LT].
    + bd_T. lstep. subst pre'. eapply BOT. reflexivity.
    + bd_F. do 2 lstep. subst pre'. eapply BOT. reflexivity.
Qed.
End Sz3.
#[using="Type"] Lemma leaf_loop : ltac:(let t := eval cbv delta [leaf_loop__stmt] in leaf_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'leaf_loop__body "vhk"). Qed.

Definition leaf_spec__stmt : Prop := forall c, ppwf c ->
  forall (raL t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d hlen,
  ppinv c m d hlen ->
  a0 = Z_to_bv 64 (c_HA c) -> a1 = Z_to_bv 64 (c_DA c) -> (64 <= c_caplen c)%Z -> (get_le32 d 60 <= 128)%Z ->
  evtF asegs (c_RNG c) (leaf_post c raL s0 s1 s2 s3 t5 t6 d hlen
               (incoming_isochronous_transfer_completed_len (mkHdr 0 0 (c_caplen c) hlen) d))
    (MS (mkR raL (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x8a078) (c_fc c) None m (seg_rom asegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_spec__stmt "v" @c).
#[using="Type"] Lemma leaf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_spec__stmt "v").
Proof.
  intros WF; intros until hlen; intros I -> -> C64 N128.
 pose proof WF as WF'. pp_init WF I.
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  pose proof (get_le32_range d 60 ZR) as ND.
  assert (RT : artcells m).
  { eapply (artcells_munch _ _ _ RT0 MU WM). repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]). apply Forall_nil. }
  destruct RT as (_ & GOT & _ & _ & SHB & _).
  carve_frame 16%nat ST.
  do 2 lstep.
  lstep. bd_F. lstep. bd_F. lstep. bd_F.
  do 3 lstep.
  zstep. ck0 UNPH; ck_go.
  zstep. ckp_at UNPD (c_DA c + 60)%Z 4%Z. do 3 zstep. lstep. ck_cut 0x8a0d0%Z [15%Z]. ckp_clear.
  rewrite ?(sx32_small (c_caplen _)) by lia.
  rd4 60%Z. lstep.
  rewrite (sx32_small (get_le32 d 60)) by lia.
  assert (LI : linv c m0 d hlen (firstn 8 junk) raL)
    by (unfold linv, FOOT; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity]).
  destruct (Z.eqb_spec (get_le32 d 60) 0) as [Z0|Z0].
  - bd_T. rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
    eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption | exact LI | reflexivity | lia]).
  - bd_F. do 2 lstep. rf_norm.
    rewrite (swrap32_small (c_caplen c + -64)) by lia.
    destruct (Z.leb_spec 16 (c_caplen c - 64)) as [B|B].
    + bd_F. do 7 lstep. rf_norm.
      replace (c_caplen c - 64)%Z with (c_caplen c - 64 - 16 * 0)%Z by lia.
      eapply (leaf_loop c WF' (Z.to_nat (get_le32 d 60 + 1)) 0%Z 0%Z);
        fastfirst (first [ noevar_assumption | exact LI | reflexivity | (f_equal; lia) | (do 2 f_equal; lia) | lia
          | (f_equal; rewrite ?swrap32_small by lia; lia) ]).
    + bd_T. rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
      eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption | exact LI | reflexivity | lia]).
Qed.
End Sz4.
#[using="Type"] Lemma leaf_spec : ltac:(let t := eval cbv delta [leaf_spec__stmt] in leaf_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'leaf_spec__body "v"). Qed.

End CANSEC1.
End F_pp_LA.

(* [comment removed for export] *)
Module F_pp_FA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_LA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma iso_data_len_loop_range : forall f nd j bl pre d,
  (0 <= pre < 2^32)%Z -> Forall (fun x => 0 <= x < 256)%Z d -> (0 <= iso_data_len_loop f nd j bl pre d < 2^32)%Z.
Proof.
  induction f as [|f IH]; intros nd j bl pre d PR ZR; cbn [iso_data_len_loop]; [lia|].
  destruct (_ && _); [|lia]. apply IH; [|exact ZR].
  destruct (negb _); [|lia].
  pose proof (u_int_sum_range (get_le32 d (64 + 16 * j + 4)) (get_le32 d (64 + 16 * j + 8))
                (get_le32_range d _ ZR) (get_le32_range d _ ZR)).
  destruct (pre <? _); lia.
Qed.
Lemma isolen_range : forall h d, (64 <= h_caplen h)%Z -> Forall (fun x => 0 <= x < 256)%Z d ->
  (0 <= incoming_isochronous_transfer_completed_len h d < 2^32)%Z.
Proof.
  intros h d HC ZR. unfold incoming_isochronous_transfer_completed_len. apply u_int_sum_range.
  - unfold iso_pseudo_header_len, u32. apply Z.mod_pos_bound. lia.
  - apply iso_data_len_loop_range; [lia | exact ZR].
Qed.

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (563832%Z, 563832%Z) => idtac | (563832%Z, 564624%Z) => idtac | (563864%Z, 563864%Z) => idtac | (563864%Z, 564776%Z) => idtac | (563892%Z, 563892%Z) => idtac | (563892%Z, 564872%Z) => idtac | (563920%Z, 563920%Z) => idtac | (563920%Z, 564980%Z) => idtac | (563952%Z, 563952%Z) => idtac | (563952%Z, 565088%Z) => idtac | (563980%Z, 563980%Z) => idtac | (563980%Z, 565180%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fixup_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) d)) d)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x89a2c) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'fixup_spec__stmt "v" @c).
#[using="Type"] Lemma fixup_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fixup_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec]. unfold USB_MAXDESC, URB_ISOCHRONOUS, URB_COMPLETE, URB_TRANSFER_IN.
  bd_F. lstep. bd_F.
  zstep. ck0 UNPH; ck_go.
  do 2 lstep. rewrite (sx32_small (c_caplen _)) by lia.
  destruct (Z.ltb_spec (c_caplen c) 64) as [C64|C64]. { bd_T. cbn [h_len]. epilog. }
  bd_F.
  bd_F. lstep. bd_F.
  pose proof (get_le32_range d 60 ZR) as ND.
  zstep. ckp_at UNPD (c_DA c + 60)%Z 4%Z. do 3 zstep. ck_cut 0x89a78%Z [15%Z]. ckp_clear.
  rd4 60%Z. run. set (nd := get_le32 d 60) in *.
  destruct (Z.ltb_spec 128 nd) as [N128|N128]. { bd_T. cbn [h_len]. epilog. }
  bd_F. rewrite ?(sx32_small nd) by lia.
  zstep. ckp_at UNPD (c_DA c + 15)%Z 1%Z. do 3 zstep. ck_cut 0x89a98%Z [16%Z]. ckp_clear.
  rd1 15%Z. run. destruct (Z.eqb_spec (get_u8 d 15) 0) as [DF|DF]; cycle 1. { bd_T. cbn [andb h_len]. epilog. }
  bd_F. cbn [andb].
  zstep. ckp_at UNPD (c_DA c + 9)%Z 1%Z. do 3 zstep. ck_cut 0x89ab4%Z [16%Z]. ckp_clear.
  rd1 9%Z. run. destruct (Z.eqb_spec (get_u8 d 9) 0) as [TT|TT]; cycle 1. { bd_T. cbn [andb h_len]. epilog. }
  bd_F. cbn [andb].
  zstep. ckp_at UNPD (c_DA c + 8)%Z 1%Z. do 3 zstep. ck_cut 0x89ad0%Z [16%Z]. ckp_clear.
  rd1 8%Z. run. destruct (Z.eqb_spec (get_u8 d 8) 67) as [ET|ET]; cycle 1. { bd_T. cbn [andb h_len]. epilog. }
  bd_F. cbn [andb].
  zstep. ckp_at UNPD (c_DA c + 10)%Z 1%Z. do 3 zstep. ck_cut 0x89af0%Z [16%Z]. ckp_clear.
  rd1 10%Z. rewrite land_128 by lia. destruct (Z.ltb_spec (get_u8 d 10) 128) as [EP|EP]; simpl_if.
  { bd_T. cbn [andb negb Z.eqb h_len]. epilog. }
  bd_F. cbn [andb negb Z.eqb Pos.eqb].
  pose proof (get_le32_range d 32 ZR) as UR.
  zstep. ckp_at UNPD (c_DA c + 32)%Z 4%Z. do 3 zstep. ck_cut 0x89b0c%Z [16%Z]. ckp_clear.
  zstep. ck0 UNPH. do 3 zstep. rd4 32%Z. ck_go.
  do 2 lstep. rf_norm. rewrite ?Z.shiftl_mul_pow2 by lia.
  unfold iso_pseudo_header_len. unfold u32.
  rewrite !(Z.mod_small (nd * 2 ^ 4) 18446744073709551616) by lia.
  rewrite (swrap32_small (nd * 2 ^ 4 + 64)) by lia.
  replace ((64 + nd * 16) mod 2 ^ 32)%Z with (nd * 2 ^ 4 + 64)%Z by (rewrite Z.mod_small by lia; lia).
  destruct (Z.ltb_spec (c_caplen c) (nd * 2 ^ 4 + 64)) as [CH|CH].
  { bd_T. match goal with |- context [c_len0 c =? ?x] => destruct (c_len0 c =? x) end; simpl_if; cbn [h_len]; epilog. }
  bd_F.
  do 2 lstep. rf_norm.
  match goal with |- context [c_len0 c =? ?x] => destruct (Z.eqb_spec (c_len0 c) x) as [LE|LE] end; cycle 1.
  { bd_T. cbn [h_len]. epilog. }
  bd_F. simpl_if.
  do 2 lstep.
  lstep.
  eapply evtF_cut; [eapply (leaf_spec c WF'); fastfirst (first [ noevar_assumption | exact I' | reflexivity | lia]) |].
  intros ms' PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & I2).
  replace (ret_pc (Z_to_bv 64 564040)) with (Z_to_bv 64 564040) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  cbn [h_caplen].
  pose proof (isolen_range (mkHdr 0 0 (c_caplen c) (c_len0 c)) d ltac:(cbn [h_caplen]; lia) ZR) as LR.
  clear HDR ZB ZW ZR LD MI MU WM ST FR UNPH UNPD LZ I'. pose proof I2 as I'. open_inv I2.
  set (LEN := incoming_isochronous_transfer_completed_len _ d) in *.
  ck0_at UNPH (c_HA c + 16)%Z; ck_go.
  lstep. rewrite (sx32_small (c_caplen _)) by lia.
  destruct (Z.leb_spec (c_caplen c) LEN) as [CL|CL]; cbn [h_len h_caplen h_sec h_usec].
  - bd_F.
    ck0_at UNPH (c_HA c + 20)%Z; ck_go.
    lstep.
    ck0_at UNPH (c_HA c + 20)%Z; ck_go. lstep.
    lstep.
    rewrite sx32_as_swrap, ltu_swrap_small by lia.
    replace ((bv_swrap 32 LEN) mod 2 ^ 32 <? c_caplen c) with false
      by (symmetry; apply Z.ltb_ge; rewrite bv_swrap32_eq; Z.div_mod_to_equations; lia).
    cbn [negb]. cbv iota.
    replace (LEN <? c_caplen c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [h_len].
    lazymatch goal with H : rw_cells _ ?mm (c_HA c) [?a; ?b; ?e; C4 ?v] |- _ =>
      pose proof (rw_cells_ext asegs mm (c_HA c) [a; b; e; C4 v] [a; b; e; C4 (Z_to_bv 64 LEN)]
         ltac:(cbn [cells_bytes cbytes]; rewrite ?le4_swrap; reflexivity) eq_refl ltac:(cbn; tauto) H) as HDR';
      clear H end.
    epilog.
  - bd_T. ck0_at UNPH (c_HA c + 20)%Z; ck_go. lstep.
    destruct (Z.ltb_spec (c_len0 c) (c_caplen c)) as [LL|LL]; cbn [h_len].
    + bd_F. ck0_at UNPH (c_HA c + 20)%Z; ck_go. lstep.
      epilog.
    + bd_T. epilog.
Qed.
End Sz3.
#[using="Type"] Lemma fixup_spec : ltac:(let t := eval cbv delta [fixup_spec__stmt] in fixup_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'fixup_spec__body "v"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fixup_spec' : forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) d)) d)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x89a24) (c_fc c) None m (seg_rom asegs)).
Proof.
  intros c WF; intros until d; intros I -> -> -> ->.
  lstep. bd_F.
  eapply fixup_spec; fastfirst (first [ noevar_assumption | exact WF | exact I | reflexivity | lia]).
Qed.

End CANSEC1.
End F_pp_FA.

(* [comment removed for export] *)
Module F_pp_DA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_pp_CA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_LA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_CA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_FA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Section CANSEC1. Context {rc : runConstT}.

#[using="Type"] Lemma artcells_here : forall c m, ppwf c -> munch (FOOT c) (c_m0 c) m -> wmono asegs (c_m0 c) m -> artcells m.
Proof.
  intros c m WF MU WM. open_wf WF.
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi. unfold FOOT in MU.
  eapply (artcells_munch _ _ _ RT0 MU WM). repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usb_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evtF asegs (c_RNG c) (ppost c (c_len0 c) (swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d false))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x894a4) (c_fc c) None m (seg_rom asegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usb_spec__stmt "v" @c).
#[using="Type"] Lemma usb_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usb_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pose proof WF as WF'.
  pose proof I as I'. destruct I' as (_ & _ & _ & _ & _ & _ & MU' & WM' & _).
  pose proof (artcells_here c m WF' MU' WM') as RT. clear MU' WM'.
  pp_init WF I.
  do 10 lstep.
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -48) |- _ =>
    release_frame FR ST (bv_unsigned spv) end.
  eapply evtF_cut.
  { eapply (usbhdr_spec c WF' false); first [ exact RT | reflexivity | lia
      | (unfold uhio; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity]) ]. }
  intros ms' PO. destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MUc & WMc & IO').
  clear HDR ZB ZW ZR LD MI ST UNPH UNPD LZ.
  unfold UW in MUc. transport_after_call asegs m m' MUc WMc.
  destruct IO' as (HDR & ZB & ZW & ZR & LD & MI & ST & UNPH & UNPD).
  apply evtF_done. unfold ppost.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.
Qed.
End Sz2.
#[using="Type"] Lemma usb_spec : ltac:(let t := eval cbv delta [usb_spec__stmt] in usb_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usb_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac close_inv := unfold ppinv, FOOT; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

Definition usbmm_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s2 = SBW ->
  evtF asegs (c_RNG c) (let D := swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d true in
             ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             s3 (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x896b0) (c_fc c) None m (seg_rom asegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbmm_spec__stmt "v" @c).
#[using="Type"] Lemma usbmm_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbmm_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof WF as WF'.
  pose proof I as I'. destruct I' as (_ & _ & _ & _ & _ & _ & MU' & WM' & _).
  pose proof (artcells_here c m WF' MU' WM') as RT. clear MU' WM'.
  pp_init WF I. cbv zeta.
  assert (ESP : bv_unsigned (SPM c) = (bv_unsigned (c_sp c) + -48)%Z) by (apply unsigned_lit; lia).
  do 6 lstep.
  eapply evtF_cut.
  { eapply (usbhdr_spec c WF' true); first [ exact RT | reflexivity | (rewrite ESP; lia)
      | (unfold uhio; rewrite ESP; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity]) ]. }
  intros ms' PO. destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MUc & WMc & IO').
  replace (ret_pc (Z_to_bv 64 562888)) with (Z_to_bv 64 562888) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  clear HDR ZB ZW ZR LD MI ST UNPH UNPD LZ.
  unfold UW in MUc. rewrite ESP in MUc. transport_after_call asegs m m' MUc WMc.
  destruct IO' as (HDR & ZB & ZW & ZR & LD & MI & ST & UNPH & UNPD). rewrite ESP in ST.
  do 3 lstep.
  eapply fixup_spec; first [exact WF' | close_inv | reflexivity].
Qed.
End Sz3.
#[using="Type"] Lemma usbmm_spec : ltac:(let t := eval cbv delta [usbmm_spec__stmt] in usbmm_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbmm_spec__body "v"). Qed.

End CANSEC1.
End F_pp_DA.
