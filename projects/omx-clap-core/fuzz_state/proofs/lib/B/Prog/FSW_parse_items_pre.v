(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) STRENGTHENED copies of parse_items' entry steps on image B for
   pi_init (a Theorem Labs lane's FSW_parse_items_init.v), which needs facts the pushed lemmas drop:
     pi_stageA5    = FSW_parse_items.pi_stageA (pushed Qed, unchanged) whose continuation also gets s5 = 2^64 - 1
                     (set at 0x84f20; pib_R0 needs it); its proof is pi_stageA's, plus that one register read;
     pi_sw1_s5     = FSW_parse_items_sw.pi_sw1 (pushed Qed, unchanged) over pi_stageA5, its continuation also getting
                     s5 = 2^64 - 1 at 0x84f5c (skip_ws keeps the callee-saved s5);
     pi_stageB_member_ro = FSW_parse_items.pi_stageB_member (pushed Qed, unchanged) run from the same state with every
                     write window closed (stage B's member arm stores nothing), its continuation also getting the
                     memory unchanged at every address (pi_init needs the frame / q / v bytes across it).
   rule 24: proves no function (kind: stage / call-step lemmas). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_calls FSW_parse_items_mem FSW_parse_items_sw FSW_parse_items_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


(* ================= closed write windows (image-free) ================= *)
(* a region with its write window closed *)
Definition pre_ro (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
Lemma pre_submem_ro : forall m, YP06.submem (map pre_ro m) m.
Proof.
induction m as [|r m IH]; cbn [map]; [apply YP06.submem_nil|].
apply YP06.submem_keep; [|exact IH].
unfold YP06.subregion, pre_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia | intros c Hc; exact Hc].
Qed.

Local Ltac pis_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Section W5. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.

(* ---- STAGE A with s5: FSW_parse_items.pi_stageA's statement and proof, the continuation also getting s5 ---- *)
Lemma pi_stageA5 : forall ly S U (W : world tfibsegs) regs mem md ch FP q ot v text len p (tb : list byte) tcap d STK
  (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK ly S U W regs mem md ch ->
  FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  0 <= d <= 1 ->
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  (forall regsC memC mat,
     pi_callA W regs regsC memC q v ->
     pi_memA W mem memC (spZ regs) q v p (text + len) d ->
     YK11.getr regsC 21 = w64 (2 ^ 64 - 1) ->
     @ajournal rc SK tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W (unpoison U memC)
       (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W memC (with_vm_backing (m_vm_lazy md) mat md) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_skip_ws regsC memC (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP q ot v text len p tb tcap d STK Q
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO Hd HFP KC.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (pi_entry SK B HSS ly S U W regs mem md ch FP q ot v text len p tb tcap d STK
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO Hd) as (HS & HJ & HARU & SHOK).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
pose proof HPRE as (HAPRE & _ & _). pose proof HAPRE as (HAR & _).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof HAPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hq47 : q <= 2 ^ 47 - 24) by lia.
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regs r) by (intros r; subst E; apply ew_Ereg_reg).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite (ER 10%bv); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite (ER 11%bv); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 d) by (subst E; rewrite fsw_ew_xatom; reflexivity).
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
unfold YG0d.cfg_at. change (w64 A_parse_items) with (Z_to_bv 64 A_parse_items).
change mem with (ms_mem (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))) in HJ at 2, HARU, SHOK.
(* ---- 0x84e70 .. 0x84f58: prologue, the UBSan / ASan checks, type 6, in->depth + 1, in->p + 1, jal skip_ws ---- *)
fsw_aj_run_to_tokU pitems_tbl_ok HS HJ HARU SHOK fs_Bspan A_skip_ws.
{ exact (pi_awr_ok B ly S W mem regs q ot v (pi_xs p (text + len) d) STK FP Hsq Hq24 HceilSTK HSTK H10 H11
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPO HFP). }
pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
pose proof (fsw_region_nth _ _ _ 3 _ HS eq_refl) as HRQ.
pose proof (fsw_region_nth _ _ _ 4 _ HS eq_refl) as HRV.
cbn [ms_mem restrict] in HR0, HRQ, HRV.
assert (FR : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs) -> ~ (q <= x < q + 24) ->
  ~ (v <= x < v + 56) -> ms_mem ms (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx H1 H2 H3. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(MState.unsigned_lit x) in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia | rewrite E10, (MState.unsigned_lit q) in Hr by lia; lia
          | rewrite E11, (MState.unsigned_lit v) in Hr by lia; lia ] |]); destruct Hin. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl).
apply (KC (ms_regs ms) (ms_mem ms) mat); [| | | exact HJ | exact HARU].
- unfold pi_callA.
  split; [pi_gw_reg HS (1%bv : bv 5); pi_gw_val; apply U_lit; lia|].
  split; [unfold spZ at 1; rewrite (fsw_reg_off _ _ _ ms 2%bv 2 (-144) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)); lia|].
  split; [pi_gw_reg HS (10%bv : bv 5); pi_gw_val; apply U_atom; [exact E10 | lia]|].
  split; [pi_gw_reg HS (8%bv : bv 5); pi_gw_val; apply U_atom_off; [exact E10 | lia | lia]|].
  split; [pi_gw_reg HS (9%bv : bv 5); pi_gw_val; apply U_atom; [exact E10 | lia]|].
  split; [pi_gw_reg HS (18%bv : bv 5); pi_gw_val; apply U_atom; [rewrite (ER 12%bv); exact H12 | lia]|].
  split; [pi_gw_reg HS (19%bv : bv 5); pi_gw_val; apply U_atom; [exact E11 | lia]|].
  split; [pi_gw_reg HS (25%bv : bv 5); pi_gw_val; exact (pi_U_shadow E 10 16 q E10 ltac:(lia) ltac:(lia) ltac:(lia) E32)|].
  split; [pi_gw_reg HS (26%bv : bv 5); pi_gw_val; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]|].
  split; [pi_gw_reg HS (27%bv : bv 5); pi_gw_val;
          rewrite (pi_U_shadow E 10 0 q E10 ltac:(lia) ltac:(lia) ltac:(lia) E32), Z.add_0_r; reflexivity|].
  split.
  { repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ =>
      pi_gw_reg HS r; rewrite fsw_SOff0; exact (ER r) end|]). apply Forall_nil. }
  unfold pi_frame, pi_saved.
  repeat (apply Forall_cons; [cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (YK11.getr regs ?r)) =>
      apply (fsw_field _ _ 2 _ _ _ _ _ _ o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0) _ HR0 E2 ltac:(cbn; tauto));
      [rewrite fsw_SOff0, ER; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
  apply Forall_nil.
- unfold pi_memA.
  assert (EQ : bv_unsigned (ew E 10) = q) by (rewrite E10; apply MState.unsigned_lit; lia).
  assert (EV : bv_unsigned (ew E 11) = v) by (rewrite E11; apply MState.unsigned_lit; lia).
  split.
  { replace q with (q + 0) at 1 by lia.
    apply (fsw_field _ _ 10 _ _ _ _ _ _ 0 8%N (SOff (xatom 0) 1) (p + 1) HRQ EQ ltac:(cbn; tauto));
      [apply bv_eq; rewrite denot_SOff, EX0, MState.unsigned_lit by lia; rewrite MState.unsigned_lit by lia;
       apply zcanon_id; unfold M64; lia | cbn; lia | cbn; lia]. }
  split.
  { apply (fsw_field _ _ 10 _ _ _ _ _ _ 8 8%N (SOff (xatom 1) 0) (text + len) HRQ EQ ltac:(cbn; tauto));
      [rewrite fsw_SOff0; exact EX1 | cbn; lia | cbn; lia]. }
  split.
  { apply (fsw_field _ _ 10 _ _ _ _ _ _ 16 4%N (SOff (xatom 2) 1) (d + 1) HRQ EQ ltac:(cbn; tauto));
      [apply bv_eq; rewrite denot_SOff, EX2, MState.unsigned_lit by lia; rewrite MState.unsigned_lit by lia;
       apply zcanon_id; unfold M64; lia | cbn; lia | cbn; lia]. }
  split.
  { replace v with (v + 0) at 1 by lia.
    apply (fsw_field _ _ 11 _ _ _ _ _ _ 0 4%N (SLit 6) 6 HRV EV ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia]. }
  split.
  { repeat (apply Forall_cons; [lazymatch goal with |- val_mem _ _ (v + ?o) 8 0 =>
      apply (fsw_field _ _ 11 _ _ _ _ _ _ o 8%N (SLit 0) 0 HRV EV ltac:(cbn; tauto)); [reflexivity | cbn; lia | cbn; lia]
      end|]). apply Forall_nil. }
  split; [exact FR|].
  exact HG.
- (* s5 = -1, set at 0x84f20 *)
  pi_gw_reg HS (21%bv : bv 5). pi_gw_val. apply U_lit. lia.
Qed.


(* ---- skip_ws #1 with s5: FSW_parse_items_sw.pi_sw1's statement and proof over pi_stageA5 ---- *)
Lemma pi_sw1_s5 : forall ly S U (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap d STK
  (ws rest : list Z) c live peak cnt fail (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  FRAME_parse_items + STK_skip_ws <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  0 <= d <= 1 ->
  ReaderRes.rest_at tb text p = 123 :: ws ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (forall c r, rest = c :: r -> PjGrammar.ws c = false) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall ly' S' (W' : world tfibsegs) regs' mem' md',
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pi_xsR (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c))
       pi_ssB0 (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs))) ->
     @ajournal rc SK tfibsegs B (STK + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md []
       ly' S' W' (unpoison U mem') md' 0 ->
     ARU tfibsegs B ly' S' U W' mem' md' ->
     spZ regs' = spZ regs - 144 ->
     YK11.getr regs' 3 = YK11.getr regs 3 -> YK11.getr regs' 4 = YK11.getr regs 4 ->
     YK11.getr regs' 8 = w64 (q + 16) -> YK11.getr regs' 9 = w64 q -> YK11.getr regs' 18 = w64 1 ->
     YK11.getr regs' 19 = w64 v -> YK11.getr regs' 25 = w64 (pi_sh (q + 16)) ->
     YK11.getr regs' 26 = w64 SHADOW_OFF -> YK11.getr regs' 27 = w64 (pi_sh q) ->
     YK11.getr regs' 21 = w64 (2 ^ 64 - 1) ->
     PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + 1 + Z.of_nat (length ws)) (d + 1) tb ->
     rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     fs_glob tfibsegs W' mem' live peak cnt fail ->
     ablocks B ly' S' = ablocks B ly S ->
     arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
     (forall a, spZ regs <= a < ot -> ~ (q <= a < q + 24) ->
        mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a /\
        (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W') mem') a)) ->
     (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i)) ->
     (forall a, v <= a < v + 56 -> exists b, Mem.mrd tfibsegs (mrestrict (w_H W') mem') (Mem.wa a) = Some b) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x84f5c) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros ly S U W regs mem md ch q ot v text len p tb tcap d STK ws rest c live peak cnt fail Q
  HPRE HHEADS HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HVSP HVTX Hd HREST Hws Hstop HGLOB K.
set (FP := [(v, v + 56)] ++ FS_PSTAT_FP).
pose proof HPRE as (HPREU & HRO).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B STK ly S U W regs mem md ch HPREU) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAPRE & _ & _). pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
destruct (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
pose proof (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR HPO) as Hvimg.
pose proof HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison U mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
assert (HSTKf : FRAME_parse_items = 144) by reflexivity.
assert (HSW0 : 0 <= STK_skip_ws) by (vm_compute; discriminate).
(* the text after `{`: in->p + 1 < in->end and the rest at p + 1 *)
pose proof (pi_rest_len _ q text len p d tb HIN) as Hrl. rewrite HREST in Hrl. cbn [length] in Hrl.
assert (Hp1 : p + 1 <= text + len) by lia.
assert (HREST1 : ReaderRes.rest_at tb text (p + 1) = ws ++ rest)
  by exact (pim_rest_skip tb text p [123] (ws ++ rest) ltac:(lia) HREST).
assert (HFP : forall a, v <= a < v + 56 -> inFP FP a)
  by (intros a Ha; exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
(* ---- stage A ---- *)
apply (pi_stageA5 ly S U W regs mem md ch FP q ot v text len p tb tcap d STK Q HPREU ltac:(lia) H10 H11 H12
  HIN HWIN HTX HPO HZERO Hd HFP).
intros regsC memC mat HCA HMA R21 HJ HARU.
set (mdC := with_vm_backing (m_vm_lazy md) mat md) in *.
destruct HCA as (R1 & Rsp & R10 & R8 & R9 & R18 & R19 & R25 & R26 & R27 & RF & HFR).
destruct HMA as (Vp & Ve & Vd & Vv0 & Vvz & FR & MG).
assert (RF' : forall r : bv 5, In r [3; 4; 20; 22; 23; 24]%bv -> YK11.getr regsC r = YK11.getr regs r)
  by (intros r Hr; rewrite Forall_forall in RF; exact (RF r Hr)).
(* the bytes stage A did not write: outside the frame, struct pj_in and v *)
assert (FRm : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 144 <= x < spZ regs) -> ~ (q <= x < q + 24) ->
  ~ (v <= x < v + 56) -> mrestrict (w_H W) memC (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x))
  by (intros x Hx H1 H2 H3; unfold mrestrict; rewrite (FR x Hx H1 H2 H3); reflexivity).
assert (EQtx : pim_eqon (mrestrict (w_H W) mem) (mrestrict (w_H W) memC) (text - HEAD) (text + tcap))
  by (intros a Ha; apply FRm; unfold HEAD in *; lia).
(* ---- skip_ws' data premises at the call ---- *)
assert (HIN1 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) memC) q text len (p + 1) (d + 1) tb).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JP & _).
  apply (pis_in_mk _ (mrestrict (w_H W) mem) q text len (p + 1) (d + 1) p d tb HIN Vp Ve Vd).
  - intros i Hi. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W memC mdC (q + i) HARU); [lia|]. apply JP. lia.
  - eapply pim_eqon_sub; [exact EQtx | unfold HEAD; lia | lia].
  - lia.
  - lia. }
assert (HTX1 : rd_text tfibsegs B ly S W memC text len tcap).
{ split; [exact Htx4096|]. split; [|exact Htxlen].
  destruct Htxblk as (TB1 & TB2 & TB3 & TB4). split; [exact TB1|]. split; [exact TB2|]. split; [exact TB3|].
  apply (pim_eqon_val (mrestrict (w_H W) mem) _ (text - HEAD) 8 tcap); [|exact TB4].
  eapply pim_eqon_sub; [exact EQtx | lia | cbn; unfold HEAD in *; lia]. }
assert (NIMGv : forall a, v <= a < v + 56 -> ~ in_img tfibsegs a).
{ intros a Ha. destruct HPO as [[((cid & pos & Hin & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
  - exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos a HAR Hin ltac:(lia)).
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR Hb ltac:(unfold HEAD in H1; lia)). }
assert (KIMG : forall a, in_img tfibsegs a -> mrestrict (w_H W) memC (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha. pose proof (fs_segs_img a Ha) as Hlo. unfold FS_IMG_END in Hlo.
  apply FRm; [lia | lia | lia |].
  intros Hv. exact (NIMGv a Hv Ha). }
assert (HG1 : fs_glob tfibsegs W memC live peak cnt fail).
{ apply (pim_glob_eqon W W mem memC live peak cnt fail); [|exact HGLOB].
  intros a Ha. exact (KIMG a (pim_pstat_img a Ha)). }
assert (HRO1 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memC)).
{ apply (pim_ro_keep B (aview tfibsegs (w_H W) mem)); [exact HRO|].
  intros a Ha. apply aview_eq_of. exact (KIMG a (fsw_roP_img a Ha)). }
(* ---- the call ---- *)
apply (pic_call_sw SK B HSW (STK + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S U W memC mdC 0 regsC
  q text len (p + 1) (d + 1) tb tcap ws rest live peak cnt fail Q HJ HARU HRO1 HHEADS).
- rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
- unfold raZ. rewrite R1. unfold w64. rewrite wz by lia. lia.
- rewrite (RF' 3%bv ltac:(cbn; tauto)). exact Hgp.
- rewrite (RF' 4%bv ltac:(cbn; tauto)). exact Htp.
- exact R10.
- exact R8.
- rewrite Rsp. rewrite Zminus_mod, Hal16. reflexivity.
- rewrite Rsp. lia.
- rewrite Rsp. lia.
- lia.
- exact HIN1.
- exact HTX1.
- exact HREST1.
- exact Hws.
- exact Hstop.
- exact HG1.
- intros ly' S' W' regs' mem' md' HJc OK' PO' HP QIN QWK QAB QTX QGL.
  rewrite R1. change (w64 0x84f5c) with (Z_to_bv 64 0x84f5c).
  set (xs := pi_xsR (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c).
  set (E := Ereg regs' (fs_extraT ++ xs)).
  assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr regsC r)
    by (intros r Hr; exact (fsw_pres _ _ r HP Hr)).
  assert (G2 : spZ regs' = spZ regs - 144) by (unfold spZ; rewrite (P 2%bv ltac:(pis_cs)); exact Rsp).
  assert (G9 : YK11.getr regs' 9 = w64 q) by (rewrite (P 9%bv ltac:(pis_cs)); exact R9).
  assert (G19 : YK11.getr regs' 19 = w64 v) by (rewrite (P 19%bv ltac:(pis_cs)); exact R19).
  assert (E2 : bv_unsigned (ew E 2) = spZ regs - 144) by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact G2).
  assert (E9 : bv_unsigned (ew E 9) = q)
    by (unfold E; rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9; unfold w64; apply wz; lia).
  assert (E19 : bv_unsigned (ew E 19) = v)
    by (unfold E; rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; unfold w64; apply wz; lia).
  destruct (pi_xsR_nth (p + 1 + Z.of_nat (length ws)) (text + len) (d + 1) regs 0 0 0 0 c)
    as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
  fold xs in X0, X1, X2, XR, X16, X17, X18, X19, X20.
  assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
  (* v's bytes across skip_ws: block or frame bytes off its empty footprint *)
  assert (VK : pim_eqon (mrestrict (w_H W) memC) (mrestrict (w_H W') mem') v (v + 56)).
  { intros x Hx.
    refine (proj2 (fsw_journal_kept_byte B _ _ _ ly S U W memC mdC ly' S' U W' mem' md' 0 x HJc HARU OK' PO' _
      (pim_inFP_nil x))).
    destruct HPO as [[((cid & pos & Hin & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
    - right. exists cid, pos. split; [exact Hin | lia].
    - left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia]. }
  assert (VWC : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) memC) (v + i))
    by (intros i Hi; apply (writable_at_grows tfibsegs (mrestrict (w_H W) mem)); [exact MG | exact (proj2 HPO i Hi)]).
  assert (VW' : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i))
    by (intros i Hi; apply (pim_eqon_wrat (mrestrict (w_H W) memC)); [eapply pim_eqon_sub; [exact VK | lia | lia] | exact (VWC i Hi)]).
  (* the frame across skip_ws: [sp - 144, sp) lies in skip_ws' window off in->p *)
  assert (HFR' : pi_frame (mrestrict (w_H W') mem') (spZ regs) regs).
  { apply (pis_frame_mb (mrestrict (w_H W) memC)); [|exact HFR].
    intros a Ha. exact (proj1 (QWK a ltac:(rewrite Rsp; lia) ltac:(lia))). }
  (* the resume *)
  pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ QIN) as (_ & _ & _ & Hp' & _).
  assert (HCS : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W') mem') (spZ regs - 144)) pi_cs)
    by exact (pis_frame_chunks regs' xs _ (spZ regs) regs XR HFR').
  assert (HRS : Forall (YP09.region_ok tfibsegs E (mrestrict (w_H W') mem')) [pi_qR; pi_vR]).
  { constructor; [|constructor; [|constructor]].
    - apply (pis_q_ok E _ q text len (p + 1 + Z.of_nat (length ws)) (d + 1) tb E9);
        [rewrite EXn; exact X0 | rewrite EXn; exact X1 | rewrite EXn; exact X2 | exact QIN].
    - unfold pi_vR, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (VW' o ltac:(lia))|].
      assert (VZ : forall o, In o [8; 16; 24; 32; 40; 48] -> val_mem tfibsegs (mrestrict (w_H W') mem') (v + o) 8 0).
      { intros o Ho. rewrite Forall_forall in Vvz. apply (pim_eqon_val (mrestrict (w_H W) memC)); [|exact (Vvz o Ho)].
        cbn [In] in Ho. eapply pim_eqon_sub; [exact VK | |]; repeat (destruct Ho as [<-|Ho]; [lia|]); destruct Ho. }
      assert (V6 : val_mem tfibsegs (mrestrict (w_H W') mem') (v + 0) 4 6).
      { rewrite Z.add_0_r. apply (pim_eqon_val (mrestrict (w_H W) memC)); [|exact Vv0].
        eapply pim_eqon_sub; [exact VK | lia | cbn; lia]. }
      constructor; [apply (chunk_ok_val tfibsegs E _ v 0 4 (SLit 6) 6); [reflexivity | cbn; lia | cbn; lia | exact V6]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 8 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 16 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 24 8 (SOff (xatom 16) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X16 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 32 8 (SOff (xatom 17) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X17 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 40 8 (SOff (xatom 18) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X18 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor; [apply (chunk_ok_val tfibsegs E _ v 48 8 (SOff (xatom 19) 0) 0);
        [rewrite fsw_SOff0, EXn; exact X19 | cbn; lia | cbn; lia | apply VZ; cbn; tauto]|].
      constructor. }
  assert (HPD : YP09.pairwise_disjoint E (fsT_ret_regions 144 pi_cs [pi_qR; pi_vR])).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pi_qR, pi_vR, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2, E9, E19.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (HGF : atoms_ok E pi_gfR).
  { unfold pi_gfR. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E19, EXn, EXn, EXn, X0, X1, X2. rewrite !MState.unsigned_lit by lia.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r. unfold HEAD in *.
    split; [split; [lia | split; [exact Hq8 | lia]]|].
    assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
    split; [split; [lia | split; [exact Hv8 | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
    split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]]. }
  destruct (pic_after_callT B (STK + (ot - spZ regs)) ot FP [] ly S U W mem md W ly S U memC mdC 0 STK_skip_ws []
    (spZ regs) 144 regsC ly' S' U W' regs' mem' md' 0 xs pi_cs [pi_qR; pi_vR] pi_gfR 0x84f5c (proj1 HSS) (proj2 HSS)
    HJ HARU HJc ltac:(intros a Ha; exfalso; exact (pim_inFP_nil a Ha)) OK' PO' HP ltac:(rewrite Rsp; lia) ltac:(lia)
    HSW0 ltac:(rewrite Rsp, Zminus_mod, Hal16; reflexivity) ltac:(lia) ltac:(rewrite Rsp; lia)
    ltac:(vm_compute; reflexivity) HCS HRS HPD HGF) as (HJ2 & HARU2 & HST).
  change (0 + 0) with 0 in HJ2.
  apply (K ly' S' W' regs' mem' md' HST HJ2 HARU2 G2).
  + rewrite (P 3%bv ltac:(pis_cs)). exact (RF' 3%bv ltac:(cbn; tauto)).
  + rewrite (P 4%bv ltac:(pis_cs)). exact (RF' 4%bv ltac:(cbn; tauto)).
  + rewrite (P 8%bv ltac:(pis_cs)). exact R8.
  + exact G9.
  + rewrite (P 18%bv ltac:(pis_cs)). exact R18.
  + exact G19.
  + rewrite (P 25%bv ltac:(pis_cs)). exact R25.
  + rewrite (P 26%bv ltac:(pis_cs)). exact R26.
  + rewrite (P 27%bv ltac:(pis_cs)). exact R27.
  + rewrite (P 21%bv ltac:(pis_cs)). exact R21.
  + exact QIN.
  + exact QTX.
  + exact QGL.
  + exact QAB.
  + exact (arodata_kept B _ _ _ ly S U W memC mdC ly' S' U W' mem' md' 0 HJc HARU OK' PO' pis_sink_nil
      (fun a _ => pim_inFP_nil a) HRO1).
  + intros a Ha Hq. rewrite Rsp in QWK. destruct (QWK a ltac:(lia) ltac:(lia)) as (M1 & W1).
    assert (Em : mrestrict (w_H W) memC (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply FRm; lia).
    rewrite M1. split; [exact (pim_mb_of_mr _ _ _ _ a Em)|].
    rewrite <- W1. apply pim_wr_keep. exact Em.
  + exact VW'.
  + intros a Ha.
    assert (H0 : exists b, Mem.mrd tfibsegs (mrestrict (w_H W) mem) (Mem.wa a) = Some b).
    { destruct HZERO as (_ & (_ & _ & HZB)).
      pose proof (HZB (Z.to_nat (a - v)) ltac:(rewrite repeat_length; lia)) as Hx.
      rewrite pi_nth_repeat in Hx by lia. rewrite Z2Nat.id in Hx by lia. replace (v + (a - v)) with a in Hx by lia.
      eexists. exact Hx. }
    destruct (pis_mrd_grows _ _ (Mem.wa a) MG H0) as (b & Hb).
    exists b. unfold Mem.mrd, Mem.wa in *. rewrite (VK a Ha). exact Hb.
Qed.
End W5.

(* ================= STAGE B's member arm, its continuation also keeping every byte ================= *)
(* FSW_parse_items.pi_stageB_member's statement and proof (pushed, unchanged), the run started from the same state with
   every write window closed (pik_setm over pre_ro: stage B's member arm 0x84f5c .. 0x84fac stores nothing), so the
   continuation also gets the memory unchanged at every address *)
Section WB5. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

Lemma pi_stageB_member_ro : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs0 regsR memR mdR
  (STK ot sp0 : Z) (FP : list (Z * Z)) kj q v p e d kids keys n cap c
  (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap c)) pi_ssB0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR kj ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 144 -> sp0 <= ot -> ot - STK <= sp0 - 144 ->
  YK11.getr regsR 8 = w64 (q + 16) -> YK11.getr regsR 9 = w64 q -> YK11.getr regsR 18 = w64 1 ->
  YK11.getr regsR 19 = w64 v -> YK11.getr regsR 25 = w64 (pi_sh (q + 16)) ->
  YK11.getr regsR 26 = w64 SHADOW_OFF -> YK11.getr regsR 27 = w64 (pi_sh q) ->
  2 ^ 46 <= q -> sp0 <= q -> q + 24 <= ot -> q + 24 <= 2 ^ 47 ->
  4096 <= v -> v + 56 <= alloc_ceiling ->
  4096 <= p -> p + 1 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 1 <= d <= 2 ->
  0 <= kids < 2 ^ 64 -> 0 <= keys < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  p < e -> 0 <= c <= 255 -> c <> 125 ->
  val_mem tfibsegs (mrestrict (w_H W) memR) p 1 c ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF q 24 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF v 56 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF p 1 ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, p <= a < p + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (v + 56 <= 0x10000 \/ FS_IMG_END <= v) -> (p + 1 <= 0x10000 \/ FS_IMG_END <= p) ->
  (v + 56 <= sp0 - 144 \/ ot <= v) -> (p + 1 <= sp0 - 144 \/ ot <= p) -> (p + 1 <= q \/ q + 24 <= p) ->
  (p + 1 <= v \/ v + 56 <= p) ->
  (forall a, v <= a < v + 56 ->
     awr_byte tfibsegs B STK ot FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall regsC memC mat,
     YK11.getr regsC 1 = w64 0x84fb0 -> spZ regsC = sp0 - 144 -> YK11.getr regsC 10 = w64 v ->
     YK11.getr regsC 8 = w64 (q + 16) -> YK11.getr regsC 9 = w64 q -> YK11.getr regsC 18 = w64 1 ->
     YK11.getr regsC 19 = w64 v -> YK11.getr regsC 20 = w64 (q + 8) ->
     YK11.getr regsC 23 = w64 (pi_sh (q + 8)) -> YK11.getr regsC 25 = w64 (pi_sh (q + 16)) ->
     YK11.getr regsC 26 = w64 SHADOW_OFF -> YK11.getr regsC 27 = w64 (pi_sh q) ->
     Forall (fun r => YK11.getr regsC r = YK11.getr regsR r) [3; 4; 21; 22; 24]%bv ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
        memC (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     (forall x, 0 <= x < 2 ^ 64 -> memC (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) memC) ->
     @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memC)
       (with_vm_backing (m_vm_lazy mdR) mat mdR) kj ->
     ARU tfibsegs B lyc Sc Uc W memC (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_grow regsC memC (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs0 regsR memR mdR STK ot sp0 FP kj q v p e d kids keys n cap c Q
  HS HJ HARU Hsp Hsot Hlo R8 R9 R18 R19 R25 R26 R27
  Hq46 Hqsp Hqot Hq47 Hv1 Hv2 Hp1 Hp2 He Hd Hki Hky Hn Hcap Hpe Hc Hc125 HBV HRAq HRAv HRAp Happv Happp
  Himgv Himgp Hvsp Hpsp Hpq Hpv HWO KC.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
set (E := Ereg regsR (fs_extraT ++ pi_xsR p e d regs0 kids keys n cap c)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (xatom j) = nth j (pi_xsR p e d regs0 kids keys n cap c) (Z_to_bv 64 0))
  by (intros j; subst E; apply fsw_ew_xatom).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (ER 2%bv); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (ER 9%bv); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (ER 19%bv); exact R19).
destruct (pi_xsR_nth p e d regs0 kids keys n cap c) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20).
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (rewrite EX; exact X0).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 e) by (rewrite EX; exact X1).
assert (EX20 : ew E (xatom 20) = Z_to_bv 64 c) by (rewrite EX; exact X20).
(* ---- the cursor byte's atom fact ---- *)
assert (AFC : afact_ok E (xatom 20) (mkAF 0 255 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EX20, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_add_fact tfibsegs _ _ _ (xatom 20) (mkAF 0 255 0) HS AFC) as HSc. clear HS.
(* ---- the five re-seats: s0 = q + 16, s2 = 1, s9 = shadow (q + 16), s10 = SHADOW_OFF, s11 = shadow q ---- *)
assert (D8 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 8%bv
  = sv_denot E (SOff 9 16)).
{ cbn [ms_regs mkst]. rewrite R8. symmetry. apply bv_eq.
  change (bv_unsigned (sv_denot E (SOff 9 16))) with (YP0e.U E (SOff 9 16)).
  rewrite (U_atom_off E 9 q 16 E9 ltac:(lia) ltac:(lia)). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (D18 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 18%bv
  = sv_denot E (SLit 1)) by (cbn [ms_regs mkst]; rewrite R18; reflexivity).
assert (D25 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 25%bv
  = sv_denot E (pi_shx 9 16)).
{ cbn [ms_regs mkst]. rewrite R25. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 16))) with (YP0e.U E (pi_shx 9 16)).
  unfold pi_shx. symmetry. exact (pi_U_shadow E 9 16 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32). }
assert (D26 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 26%bv
  = sv_denot E (SOff 32 0)) by (cbn [ms_regs mkst]; rewrite R26, fsw_SOff0, E32; reflexivity).
assert (D27 : YK11.getr (ms_regs (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) 27%bv
  = sv_denot E (pi_shx 9 0)).
{ cbn [ms_regs mkst]. rewrite R27. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold pi_sh, SHADOW_OFF; lia).
  change (bv_unsigned (sv_denot E (pi_shx 9 0))) with (YP0e.U E (pi_shx 9 0)).
  unfold pi_shx. rewrite (pi_U_shadow E 9 0 q E9 ltac:(lia) ltac:(lia) ltac:(lia) E32), Z.add_0_r. reflexivity. }
apply (st_ok_set_reg tfibsegs E _ _ 8%bv (SOff 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D8].
apply (st_ok_set_reg tfibsegs E _ _ 18%bv (SLit 1)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D18].
apply (st_ok_set_reg tfibsegs E _ _ 25%bv (pi_shx 9 16)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D25].
apply (st_ok_set_reg tfibsegs E _ _ 26%bv (SOff 32 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D26].
apply (st_ok_set_reg tfibsegs E _ _ 27%bv (pi_shx 9 0)) in HSc;
  [| discriminate | cbn [ms_regs restrict mkst]; exact D27].
(* ---- the cursor byte as a region, and in->p < in->end ---- *)
assert (RB : region_ok tfibsegs E (mrestrict (w_H W) memR) pi_byte).
{ unfold region_ok, pi_byte.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EX0, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ p 0 1 (SOff (xatom 20) 0) c);
    [rewrite fsw_SOff0; exact EX20 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact HBV. }
assert (DJ : all_disjoint E pi_byte (ss_mem pi_ssB0)).
{ apply all_disjoint_of_extents.
  unfold pi_ssB0, fss_retT, fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pi_qR, pi_vR, pi_byte,
    extent_of_region.
  cbn [ss_mem app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite EX0, E2, E9, E19, !unsigned_lit_small by lia.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END
    in Himgp |- *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
apply (st_ok_add_region' tfibsegs E _ _ pi_byte) in HSc;
  [| vm_compute; reflexivity | cbn [ms_mem restrict]; exact RB | cbn [ss_mem]; exact DJ].
assert (CC1 : branch_taken BC_LTU (sv_denot E (SOff (xatom 0) 0)) (sv_denot E (SOff (xatom 1) 0)) = true).
{ rewrite branch_ltu_U, (U_atom E (xatom 0) p EX0 ltac:(lia)), (U_atom E (xatom 1) e EX1 ltac:(lia)).
  apply Z.ltb_lt. lia. }
apply (st_ok_add_cond tfibsegs E _ _ BC_LTU (SOff (xatom 0) 0) (SOff (xatom 1) 0)) in HSc; [| exact CC1].
(* ---- the brace test: the byte is not `}` ---- *)
assert (CC2 : branch_taken BC_EQ (sv_denot E (SLit 125)) (sv_denot E (SOff (xatom 20) 0)) = false).
{ rewrite branch_eq_U, U_lit by lia. rewrite (U_atom E (xatom 20) c EX20 ltac:(lia)).
  apply Z.eqb_neq. lia. }
apply (st_ok_add_cond_neg tfibsegs E _ _ BC_EQ (SLit 125) (SOff (xatom 20) 0)) in HSc; [| exact CC2].
(* ---- the three shadow entries ---- *)
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF)
  by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok tfibsegs fs_Bx pi_SHR E (mrestrict (w_H W) memR)).
{ unfold sh_ok, pi_SHR. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 9 q 24 q 0 24 HRAq UB
      ltac:(apply U_atom; [exact E9 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx 19 v 56 v 0 56 HRAv UB
      ltac:(apply U_atom; [exact E19 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happv. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E fs_Bx (xatom 0) p 1 p 0 1 HRAp UB
      ltac:(apply U_atom; [exact EX0 | lia])); [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. apply Happp. lia. }
(* ---- NEW: every write window closed (stage B's member arm stores nothing), so the run keeps every byte ---- *)
lazymatch type of HSc with st_ok _ _ ?s0 _ =>
  pose proof (pik_st_ok_setm _ s0 _ (map pre_ro (ss_mem s0)) HSc (pre_submem_ro (ss_mem s0))
    ltac:(vm_compute; reflexivity)) as HSc2 end.
clear HSc. rename HSc2 into HSc.
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x84f5c) memR (seg_rom tfibsegs))) in HJ, HARU, SHOK.
(* ---- 0x84f5c .. 0x84fac: the shadow checks, the end test, the cursor byte, jal grow ---- *)
fsw_aj_run_to_tokU pitems_tbl_ok HSc HJ HARU SHOK fs_Bspan A_grow.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ee ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ee rs' a1 a2 a3 a4 a5 a6 a7 a8) end.
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
assert (ALL : forall x, 0 <= x < 2 ^ 64 -> ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)).
{ intros x Hx. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]); destruct Hin. }
assert (FR : forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 144 <= x < sp0) -> ~ (q <= x < q + 24) -> ~ (v <= x < v + 56) ->
  ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) by (intros x Hx _ _ _; exact (ALL x Hx)).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl).
lazymatch type of HSc with st_ok _ ?Ee _ _ => set (E' := Ee) in * end.
assert (EE : forall j, (j < 54)%nat -> ew E' j = ew E j)
  by (intros j Hj; unfold E'; rewrite !ew_ewset_other by lia; reflexivity).
assert (ER' : forall r : bv 5, ew E' (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; pose proof (u5_range r); rewrite EE by lia; exact (ER r)).
assert (E2' : bv_unsigned (ew E' 2) = sp0 - 144) by (rewrite EE by lia; exact E2).
assert (E9' : ew E' 9 = Z_to_bv 64 q) by (rewrite EE by lia; exact E9).
assert (E19' : ew E' 19 = Z_to_bv 64 v) by (rewrite EE by lia; exact E19).
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EE by lia; exact E32).
apply (KC (ms_regs ms) (ms_mem ms) mat);
  [ | | | | | | | | | | | | | exact FR | exact ALL | exact HG | exact HJ | exact HARU].
- pi_gw_reg HSc (1%bv : bv 5). pi_gw_val. apply U_lit. lia.
- unfold spZ at 1.
  rewrite (fsw_reg_off _ _ _ ms 2%bv 2 0 (sp0 - 144) HSc ltac:(vm_compute; reflexivity) E2' ltac:(lia)). lia.
- pi_gw_reg HSc (10%bv : bv 5). pi_gw_val. apply U_atom; [exact E19' | lia].
- pi_gw_reg HSc (8%bv : bv 5). pi_gw_val. apply U_atom_off; [exact E9' | lia | lia].
- pi_gw_reg HSc (9%bv : bv 5). pi_gw_val. apply U_atom; [exact E9' | lia].
- pi_gw_reg HSc (18%bv : bv 5). pi_gw_val. apply U_lit. lia.
- pi_gw_reg HSc (19%bv : bv 5). pi_gw_val. apply U_atom; [exact E19' | lia].
- pi_gw_reg HSc (20%bv : bv 5). pi_gw_val. apply U_atom_off; [exact E9' | lia | lia].
- pi_gw_reg HSc (23%bv : bv 5). pi_gw_val.
  exact (pi_U_shadow E' 9 8 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32').
- pi_gw_reg HSc (25%bv : bv 5). pi_gw_val.
  exact (pi_U_shadow E' 9 16 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32').
- pi_gw_reg HSc (26%bv : bv 5). pi_gw_val. apply U_atom; [exact E32' | unfold SHADOW_OFF; lia].
- pi_gw_reg HSc (27%bv : bv 5). pi_gw_val.
  rewrite (pi_U_shadow E' 9 0 q E9' ltac:(lia) ltac:(lia) ltac:(lia) E32'), Z.add_0_r. reflexivity.
- repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ =>
    pi_gw_reg HSc r; rewrite fsw_SOff0; exact (ER' r) end|]). apply Forall_nil.
Qed.

End WB5.
