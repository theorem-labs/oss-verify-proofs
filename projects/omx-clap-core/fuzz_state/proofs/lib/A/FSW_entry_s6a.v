(* fs program part, lane ENTRY, segment S6 (fs.asan 0x8108c-0x810c4, fs.c:328-333), PART A: what the six PROGRAM calls
   of the segment share. S6 is `live = fuzz_alloc_live (); fuzz_alloc_peak_reset (); body = preset_base64_decode (text,
   &len); peak = fuzz_alloc_peak (); check_bounded_alloc (peak - live, n); check_as_written (text, body, len)`, six
   calls with no store of the walk's own between them, so one recipe serves all six: read the call site's registers off
   the canonical state (FSW_entry_defs.v fe_ss), build the callee's fpreU from the walk's journal (YCbq afn_pre_at) and
   ARU, apply the callee's spec, compose its fpostU journal into the walk's with FSW_K3.fsw_ajournal_sub5 and rebuild
   the canonical state with FSW_entry_canon.fe_canon.
   This file proves that recipe once (s6_fpreU, s6_resume) plus the facts the six calls read and carry (the call site's
   frame chunks, the bytes a callee keeps, the read-only view, src_rd of a live block). S6's own call chain is in
   FSW_entry_s6.v. rule 24: no function proved. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0s YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_K3 FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import ACfn FSH_Harness FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSW_entry_defs FSW_entry_canon FSW_entry_ar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require ACem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s6a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the entry's own geometry ---- *)
(* the entry sp and the re-aligned sp: `addi sp, sp, -96` then `andi sp, sp, -32` (0x80f1c / 0x80f54) *)
Lemma s6_sp0 : forall cx, fe_base B cx ->
  fe_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= fe_sp0 cx /\ fe_sp0 cx <= 2 ^ 47 /\
  fe_sp0 cx - 112 <= fe_sp1 cx <= fe_sp0 cx - 96 /\ fe_sp1 cx mod 16 = 0.
Proof.
intros cx ((HAP & _) & _).
pose proof (fsw_sp_pre B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] HAP)
  as (Hal & Hceil & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hal0 : fe_sp0 cx mod 16 = 0) by exact Hal.
assert (Hc0 : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by exact Hceil.
assert (H470 : fe_sp0 cx <= 2 ^ 47) by exact H47.
assert (Hx : (fe_sp0 cx - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal0; reflexivity).
pose proof (fsw_realign_facts (fe_sp0 cx - 96) ltac:(unfold LLVMF_STK in *; lia) Hx) as (R1 & _ & R3).
unfold fe_sp1. split; [exact Hal0|]. split; [exact Hc0|]. split; [exact H470|]. split; [lia | exact R3].
Qed.

(* the extra atoms 44 / 45 of fe_extra (the flag address and the frame's shadow address) *)
Lemma s6_eFL : forall cx E, fe_E cx E -> ew E 44 = Z_to_bv 64 (fe_FL cx).
Proof.
intros cx E H. change 44%nat with (32 + 12)%nat. rewrite (H 12%nat ltac:(lia)).
unfold fe_extra, fe_saved_regs. cbn [map nth app]. reflexivity.
Qed.
Lemma s6_eSF : forall cx E, fe_E cx E -> ew E 45 = Z_to_bv 64 (fe_SF cx).
Proof.
intros cx E H. change 45%nat with (32 + 13)%nat. rewrite (H 13%nat ltac:(lia)).
unfold fe_extra, fe_saved_regs. cbn [map nth app]. reflexivity.
Qed.

(* the walk's journal at any boundary: the entry's own fake frame is the only live one, and the layout kept it *)
Lemma s6_walk : forall cx lyc Sc (W : world tfibsegs) memc mdc k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W memc mdc k ->
  frames Sc = [(0, c_fpos cx)] /\ In (0, c_fpos cx) (frames Sc) /\
  ly_F lyc = ly_F (c_ly cx) /\ ly_top lyc = ly_top (c_ly cx) /\
  frame_addr lyc 0 (c_fpos cx) = fe_F cx /\ flag_addr lyc 0 (c_fpos cx) = fe_FL cx.
Proof.
intros cx lyc Sc W memc mdc k ((HAP & _ & _ & _ & _ & _ & _ & Hfr0 & _) & _) HJ.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & _).
assert (Efrs : frames Sc = [(0, c_fpos cx)]) by (rewrite Hfrs, Hfr0; reflexivity).
split; [exact Efrs|]. split; [rewrite Efrs; left; reflexivity|].
split; [exact EF|]. split; [exact Etop|].
split; unfold fe_F, fe_FL, frame_addr, flag_addr; rewrite EF; reflexivity.
Qed.

(* the frame's position in memory, from AR at the boundary *)
Lemma s6_geom : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc,
  ARU tfibsegs B lyc Sc Uc W memc mdc -> In (0, c_fpos cx) (frames Sc) ->
  frame_addr lyc 0 (c_fpos cx) = fe_F cx -> flag_addr lyc 0 (c_fpos cx) = fe_FL cx ->
  4096 <= fe_F cx /\ fe_F cx + 64 <= alloc_ceiling /\ fe_F cx mod 32 = 0 /\
  in_app (fe_F cx) 64 /\ 0 <= fe_FL cx < alloc_ceiling /\
  kLowMemEnd <= fe_SF cx /\ fe_SF cx + 8 <= kHighShadowEnd.
Proof.
intros cx lyc Sc Uc W memc mdc HARU Hin EF EFL.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memc mdc HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc 0 (c_fpos cx) HAR Hin) as (H4096 & Hceil & Happ).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memc) mdc 0 (c_fpos cx) HAR Hin) as (Hal32 & _ & _ & _).
destruct (al_flag _ _ LAWS lyc Sc W (unpoison Uc memc) mdc 0 (c_fpos cx) HAR Hin) as (_ & _ & Hflapp & Hflc).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite EF in H4096, Hceil, Happ, Hal32. rewrite Hfb in Hceil, Happ. rewrite EFL in Hflapp, Hflc.
destruct Hflapp as [Hfl0 _].
pose proof (shadow_addr_bounds (fe_F cx) ltac:(unfold kHighMemEnd in *; lia)) as (Hs1 & Hs2).
pose proof (shadow_addr_bounds (fe_F cx + 63) ltac:(unfold kHighMemEnd in *; lia)) as (_ & Hs4).
assert (Hs5 : shadow_addr (fe_F cx) + 7 <= shadow_addr (fe_F cx + 63))
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
assert (ESF : fe_SF cx = shadow_addr (fe_F cx)) by reflexivity.
split; [lia|]. split; [lia|]. split; [exact Hal32|]. split; [exact Happ|]. split; [lia|]. rewrite ESF. lia.
Qed.

(* the write window of a canonical boundary state: the frame (own), its shadow (own), the saved words (stack) *)
Lemma s6_awr : forall cx E lyc Sc cs,
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  awr_ok tfibsegs B E (fe_regions cs) LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B lyc Sc) lyc [(0, c_fpos cx)] (frames (c_S cx)).
Proof.
intros cx E lyc Sc cs E8 E24 E25 EF.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
unfold fe_regions.
eapply awr_ok_cons_gen with (k := 24%nat) (b := fe_F cx); [reflexivity | exact E24 | |].
{ intros a Ha. cbn [fe_frame_region YP09.r_wlo YP09.r_whi] in Ha.
  left. right. right. right. exists 0, (c_fpos cx). split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. lia. }
eapply awr_ok_cons_gen with (k := 25%nat) (b := fe_SF cx); [reflexivity | exact E25 | |].
{ intros a Ha. cbn [fe_shadow_region YP09.r_wlo YP09.r_whi] in Ha. unfold fe_SF in Ha.
  left. right. right. right. exists 0, (c_fpos cx). split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. change (64 / 8) with 8. lia. }
eapply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8 | | |].
{ cbn [fs_ret_s0_region YP09.r_wlo]. unfold LLVMF_STK. lia. }
{ cbn [fs_ret_s0_region YP09.r_whi]. lia. }
apply awr_ok_nil.
Qed.

(* reading a register the run left as its entry atom *)
Lemma s6_reg_at : forall E ss ms (W : world tfibsegs) (r : bv 5) nn,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn 0 ->
  YK11.getr (ms_regs ms) r = ew E nn.
Proof.
intros E ss ms W r nn HS Hr.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hr, fsw_SOff0. reflexivity.
Qed.

(* what the canonical boundary state says about the frame: the eleven saved words, the flag word, the frame's chunks *)
Lemma s6_frame_at : forall cx E (W : world tfibsegs) ms ss cs,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_mem ss = fe_regions cs -> fe_E cx E ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> 0 <= fe_FL cx < 2 ^ 64 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_sp0 cx)) fe_sv_chunks /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (fe_F cx + 56) = Some (fe_FL cx) /\
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_F cx)) cs.
Proof.
intros cx E W ms ss cs HS Hmem HE E8 E24 HFL.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) 0%nat (fe_frame_region cs) HS
  ltac:(rewrite Hmem; reflexivity)) as HR0.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) 2%nat (fs_ret_s0_region (-88) 0 fe_sv_chunks) HS
  ltac:(rewrite Hmem; reflexivity)) as HR2.
cbn [ms_mem restrict] in HR0, HR2.
destruct HR0 as (_ & _ & _ & HC0). destruct HR2 as (_ & _ & _ & HC2).
cbn [fe_frame_region fs_ret_s0_region YP09.r_base YP09.r_chunks base_val] in HC0, HC2.
rewrite E24 in HC0. rewrite E8 in HC2.
split; [exact HC2|].
split; [|exact (Forall_inv_tail HC0)].
pose proof (Forall_inv HC0) as Hflag.
apply (ACem.rdword_of_val_mem tfibsegs (w_H W) (ms_mem ms) (fe_F cx + 56) (fe_FL cx)); [|exact HFL].
apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_F cx) 56 8%N (SOff 44 0) (fe_FL cx) Hflag);
  [rewrite fsw_SOff0; exact (s6_eFL cx E HE) | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia].
Qed.

(* ---- what a callee keeps: bytes outside its footprint ---- *)
(* the entry's fake frame *)
Lemma s6_keep_frame : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc STKc spc FPc ly' S' U' (W' : world tfibsegs)
  mem' md' kc a,
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  ajournal tfibsegs B STKc spc FPc lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (0, c_fpos cx) (frames Sc) -> frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  fe_F cx <= a < fe_F cx + 64 -> ~ inFP FPc a ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a.
Proof.
intros cx lyc Sc Uc W memc mdc STKc spc FPc ly' S' U' W' mem' md' kc a HARU HJc OK' PO' Hin EF Ha HnF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc 0 (c_fpos cx)
  (ARU_AR tfibsegs B lyc Sc Uc W memc mdc HARU) Hin) as (_ & _ & Happ).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite EF, Hfb in Happ.
pose proof (in_app_addr (fe_F cx) 64 a Happ Ha) as Hap.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
rewrite <- (mbyte_unpoison_app B ly' S' U' W' mem' md' a HARU' ltac:(unfold SHADOW_OFF in *; lia)
  ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia)).
rewrite <- (mbyte_unpoison_app B lyc Sc Uc W memc mdc a HARU ltac:(unfold SHADOW_OFF in *; lia)
  ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia)).
apply (mbyte_of_aview tfibsegs).
apply (F4 0 (c_fpos cx) a Hin); [|exact HnF].
left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF, Hfb. lia.
Qed.

(* the stack above the callee's window *)
Lemma s6_keep_stack : forall lyc Sc Uc (W : world tfibsegs) memc mdc STKc spc FPc ly' S' U' (W' : world tfibsegs)
  mem' md' kc a,
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  ajournal tfibsegs B STKc spc FPc lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (spc - STKc <= a < spc) ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a.
Proof.
intros lyc Sc Uc W memc mdc STKc spc FPc ly' S' U' W' mem' md' kc a HARU HJc OK' PO' Ha Hout.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply (mbyte_of_aview tfibsegs).
rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU' ltac:(lia)).
rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memc mdc a HARU ltac:(lia)).
apply F1; [lia | exact Hout].
Qed.

(* a block the callee keeps, outside its footprint *)
Lemma s6_keep_blk : forall lyc Sc Uc (W : world tfibsegs) memc mdc STKc spc FPc ly' S' U' (W' : world tfibsegs)
  mem' md' kc b m i,
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  ajournal tfibsegs B STKc spc FPc lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m -> ~ inFP FPc (b + i) ->
  mbyte tfibsegs (mrestrict (w_H W') mem') (b + i) = mbyte tfibsegs (mrestrict (w_H W) memc) (b + i).
Proof.
intros lyc Sc Uc W memc mdc STKc spc FPc ly' S' U' W' mem' md' kc b m i HARU HJc OK' PO' Hin Hin' Hi HnF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
destruct (al_blocks _ _ LAWS lyc Sc W (unpoison Uc memc) mdc b m
  (ARU_AR tfibsegs B lyc Sc Uc W memc mdc HARU) Hin) as (_ & _ & _ & Happ & _).
pose proof (in_app_addr b (req_size m) (b + i) Happ ltac:(lia)) as Hap.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite <- (mbyte_unpoison_app B ly' S' U' W' mem' md' (b + i) HARU' ltac:(unfold SHADOW_OFF in *; lia)
  ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia)).
rewrite <- (mbyte_unpoison_app B lyc Sc Uc W memc mdc (b + i) HARU ltac:(unfold SHADOW_OFF in *; lia)
  ltac:(unfold SHADOW_OFF, kHighMemBeg in *; lia)).
apply (mbyte_of_aview tfibsegs). exact (F2 b m i Hin Hin' Hi HnF).
Qed.

(* ---- the read-only view at a boundary: the walk's footprint holds no read-only byte ---- *)
Lemma s6_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a /\ 0 <= a < FS_IMG_END.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr].
- assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
  split; [exact Hi | exact (fsk_segs_img a Hi)].
- assert (Hi : in_img tfibsegs a).
  { unfold in_img. eexists. split; [right; right; left; reflexivity|].
    unfold FS_RLO, FS_RHI in Hr.
    match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
      let l := eval vm_compute in lo in let h := eval vm_compute in sz in
      change lo with l; change lo' with l; change sz with h end. lia. }
  split; [exact Hi | exact (fsk_segs_img a Hi)].
Qed.
(* the walk's footprint (fuzz/alloc.c's four statics, .bss at 0xa3ca0 / 0x5da5c0 / 0x5da5e0 / 0x5da600) holds no
   read-only byte: the non-writable segments end at 0x9f000 and the relro range at FS_RHI = 0xa03e8 *)
Lemma s6_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
assert (Hp : 0xa1000 <= fst r) by (repeat (destruct Hr as [<-|Hr]; [cbn; lia|]); destruct Hr).
destruct Hro as [(sg & Hsg & Hw & Hr2) | Hr2].
- assert (HB : forallb (fun s => seg_writable s ||
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) tfibsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB sg Hsg) as H. cbv beta in H. rewrite Hw in H. cbn [orb] in H.
  apply Z.leb_le in H. cbn [fst snd] in Ha, Hp. lia.
- unfold FS_RLO, FS_RHI in Hr2. cbn [fst snd] in Ha, Hp. lia.
Qed.

Lemma s6_arodata : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc).
Proof.
intros cx lyc Sc Uc W memc mdc k ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _) & _) HJ HARU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Hro Ho He.
destruct (s6_ro_img a Hro) as [Himg Hb]. unfold FS_IMG_END in Hb.
assert (Eu : aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) (unpoison Uc memc) a).
{ symmetry. apply (aview_at tfibsegs).
  exact (FSW_strkit.unpoison_app B lyc Sc Uc W memc mdc a HARU ltac:(unfold SHADOW_OFF in *; lia)
    ltac:(left; unfold SHADOW_OFF in *; lia)). }
rewrite Eu.
rewrite (F3 a Himg Ho He (s6_ro_not_pstat a Hro)
  (fp_spares_closed FS_PSTAT_FP a (sink_closed_pos FS_PSTAT_FP
     ltac:(unfold FS_PSTAT_FP; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)))).
exact (HRO a Hro Ho He).
Qed.

(* ---- the call recipe: the callee's pre at the call site, and the walk's state after the return ---- *)
(* the entry's return address and frame pointer, saved at s0 - 8 and s0 - 16 by the prologue *)
Lemma s6_eRA : forall cx E, fe_E cx E -> ew E 33 = YK11.getr (c_regs cx) 1%bv.
Proof.
intros cx E H. change 33%nat with (32 + 1)%nat. rewrite (H 1%nat ltac:(lia)).
unfold fe_extra, fe_saved_regs. cbn [map nth app]. reflexivity.
Qed.
Lemma s6_eS0 : forall cx E, fe_E cx E -> ew E 34 = YK11.getr (c_regs cx) 8%bv.
Proof.
intros cx E H. change 34%nat with (32 + 2)%nat. rewrite (H 2%nat ltac:(lia)).
unfold fe_extra, fe_saved_regs. cbn [map nth app]. reflexivity.
Qed.

(* the eleven saved words read the same under any env that carries fe_extra *)
Lemma s6_sv_env : forall cx E E' m base,
  fe_E cx E -> fe_E cx E' ->
  Forall (YP09.chunk_ok tfibsegs E m base) fe_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E' m base) fe_sv_chunks.
Proof.
intros cx E E' m base HE HE' H. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) H c Hc) as Hck.
unfold fe_sv_chunks in Hc. apply in_map_iff in Hc as (j & Ec & Hj). apply in_seq in Hj.
assert (Ej : ew E (33 + j)%nat = ew E' (33 + j)%nat).
{ change (33 + j)%nat with (32 + (1 + j))%nat. rewrite (HE (1 + j)%nat ltac:(lia)), (HE' (1 + j)%nat ltac:(lia)).
  reflexivity. }
intros i Hi. rewrite <- Ec in Hck, Hi |- *. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
cbn [YP09.c_val cbyte] in Hb1 |- *. rewrite !fsw_SOff0 in Hb1 |- *. rewrite <- Ej. exact Hb1.
Qed.

(* the two words the saved-register region holds at s0 - 8 and s0 - 16 *)
Lemma s6_sv_words : forall cx E (W : world tfibsegs) mem,
  fe_E cx E -> Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (fe_sp0 cx)) fe_sv_chunks ->
  rdword (aview tfibsegs (w_H W) mem) (fe_sp0 cx - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview tfibsegs (w_H W) mem) (fe_sp0 cx - 16) = Some (s0Z (c_regs cx)).
Proof.
intros cx E W mem HE H. unfold fe_sv_chunks in H. cbn [seq map] in H.
pose proof (Forall_inv H) as H0. pose proof (Forall_inv (Forall_inv_tail H)) as H1.
split; apply (ACem.rdword_of_val_mem tfibsegs (w_H W) mem); try (unfold raZ, s0Z; apply u64_range).
- replace (fe_sp0 cx - 8) with (fe_sp0 cx + - 8 * (Z.of_nat 0 + 1)) by (cbn; lia).
  apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) mem) (fe_sp0 cx) _ 8%N (SOff 33 0) (raZ (c_regs cx)) H0);
    [rewrite fsw_SOff0, (s6_eRA cx E HE); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
    | cbn [Z.of_N]; unfold raZ; pose proof (u64_range (YK11.getr (c_regs cx) 1%bv)); lia | cbn [Z.of_N]; lia].
- replace (fe_sp0 cx - 16) with (fe_sp0 cx + - 8 * (Z.of_nat 1 + 1)) by (cbn; lia).
  apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) mem) (fe_sp0 cx) _ 8%N (SOff 34 0) (s0Z (c_regs cx)) H1);
    [rewrite fsw_SOff0, (s6_eS0 cx E HE); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
    | cbn [Z.of_N]; unfold s0Z; pose proof (u64_range (YK11.getr (c_regs cx) 8%bv)); lia | cbn [Z.of_N]; lia].
Qed.

(* the call chain at any of the segment's call sites: the entry's own frame record, or none (the entry sp within 16
   of ly_top) *)
Lemma s6_chain : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k ->
  rdword (aview tfibsegs (w_H W) (unpoison Uc memc)) (fe_sp0 cx - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview tfibsegs (w_H W) (unpoison Uc memc)) (fe_sp0 cx - 16) = Some (s0Z (c_regs cx)) ->
  exists ch, achain lyc (aview tfibsegs (w_H W) (unpoison Uc memc)) (fe_sp1 cx) (fe_sp0 cx) ch.
Proof.
intros cx lyc Sc Uc W memc mdc k HB HJ Hra Hs0.
pose proof HB as HB'. destruct HB' as ((HAP & Hra0 & _) & _).
pose proof HAP as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch0 & _).
pose proof (s6_sp0 cx HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal1).
pose proof asan_consts as (C1 & _).
pose proof (s6_walk cx lyc Sc W (unpoison Uc memc) mdc k HB HJ) as (_ & _ & _ & Etop & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hstk as (_ & _ & Hslo & _ & Hshi & Hshi2 & _ & Htop1 & Htop2).
assert (Hkeep : forall a, fe_sp0 cx <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison Uc memc) a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a)
  by (intros a Ha; apply F1; unfold LLVMF_STK in *; lia).
assert (Htop64 : ly_top lyc <= 2 ^ 64) by (rewrite Etop; lia).
destruct (Z_lt_le_dec (fe_sp0 cx) (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
- exists [(fe_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx))].
  apply (achain_push lyc (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) _ (fe_sp0 cx) (s0Z (c_regs cx))
      (raZ (c_regs cx)) [] (fe_sp1 cx)).
  + apply (achain_ly_top (c_ly cx) lyc _ (fe_sp0 cx)); [exact Etop | exact Hch0].
  + exact Htop64.
  + exact Hkeep.
  + exact Hra.
  + exact Hs0.
  + exact Hra4.
  + unfold LLVMF_STK in *; lia.
  + pose proof (Z.div_mod (fe_sp0 cx) 16 ltac:(lia)) as Hd. rewrite Hal16 in Hd.
    replace (fe_sp0 cx) with (2 * (fe_sp0 cx / 16) * 8) by lia. apply Z_mod_mult.
  + rewrite Etop; lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* the callee's fpreU at a call site of the segment *)
Lemma s6_fpreU : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc k regsc STKc ch,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  spZ regsc = fe_sp1 cx -> 0 <= STKc -> STKc + 112 <= LLVMF_STK ->
  YK0s.ret_ok (YK11.getr regsc 1%bv) -> 4096 <= raZ regsc ->
  YK11.getr regsc 3%bv = w64 (as_gp B) -> YK11.getr regsc 4%bv = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison Uc memc)) (spZ regsc) (s0Z regsc) ch ->
  fpreU tfibsegs B STKc lyc Sc Uc W regsc memc mdc ch.
Proof.
intros cx lyc Sc Uc W memc mdc k regsc STKc ch HB HJ HARU HRO Hsp HK0 HKb Hret Hra4 Hgp Htp Hch.
pose proof (s6_sp0 cx HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal1).
destruct HARU as (_ & OK & PO).
split; [|exact HRO]. split; [|split; [exact OK | exact PO]].
apply (afn_pre_at tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k regsc STKc (fe_sp1 cx - fe_sp0 cx) ch HJ).
- rewrite Hsp. lia.
- rewrite Zminus_mod, Hal1, Hal16. reflexivity.
- lia.
- exact HK0.
- unfold LLVMF_STK in *. lia.
- exact Hret.
- exact Hra4.
- exact Hgp.
- exact Htp.
- exact Hch.
Qed.


(* the walk's state after a program call of the segment: the composed journal, ARU, and the canonical boundary state
   at the return address (FSW_K3.fsw_ajournal_sub4 then FSW_entry_canon.fe_canon) *)
Lemma s6_resume : forall cx lyc Sc Uc (W : world tfibsegs) memc mdc k STKc FPc regsc ly' S' U' (W' : world tfibsegs)
  regs' mem' md' kc E xs r cs,
  fe_base B cx -> fe_E cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  ajournal tfibsegs B STKc (spZ regsc) FPc lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  fsw_fp_sub B (c_ly cx) (c_S cx) lyc Sc [(0, c_fpos cx)] FS_PSTAT_FP FPc ->
  (forall a, fe_F cx + 56 <= a < fe_F cx + 64 -> ~ inFP FPc a) ->
  spZ regsc = fe_sp1 cx -> 0 <= STKc -> STKc + 112 <= LLVMF_STK ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) memc) (fe_sp0 cx)) fe_sv_chunks ->
  rdword (aview tfibsegs (w_H W) memc) (fe_F cx + 56) = Some (fe_FL cx) ->
  aregs_preserved regsc regs' ->
  YK11.getr regsc 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr regsc 24%bv = Z_to_bv 64 (fe_F cx) ->
  YK11.getr regsc 18%bv = Z_to_bv 64 (fe_F cx) -> YK11.getr regsc 25%bv = Z_to_bv 64 (fe_SF cx) ->
  regions_wf (fe_regions cs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 56) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (mrestrict (w_H W') mem') (fe_F cx)) cs ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (fe_ss r cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros cx lyc Sc Uc W memc mdc k STKc FPc regsc ly' S' U' W' regs' mem' md' kc E xs r cs
  HB HE HJ HARU HJc OK' PO' HFP HnF Hsp HK0 HKb Hsv Hflag HP R8 R24 R18 R25 Hwf Hcin Hcs.
pose proof (s6_sp0 cx HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s6_walk cx lyc Sc W (unpoison Uc memc) mdc k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom cx lyc Sc Uc W memc mdc HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
assert (HJ2 : ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(0, c_fpos cx)] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ exact (fsw_ajournal_sub5 B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc memc) mdc k STKc (spZ regsc) FPc [] ly' S' W' (unpoison U' mem') md' kc
    HJ HJc ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HFP). }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
pose proof (s6_walk cx ly' S' W' (unpoison U' mem') md' (k + kc) HB HJ2) as (Efrs2 & Hin2 & ELY2 & _ & _ & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* the eleven saved words at the new memory, under the resumed env *)
assert (Hsv2 : Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (mrestrict (w_H W') mem') (fe_sp0 cx))
  fe_sv_chunks).
{ pose proof (s6_sv_env cx E (Ereg regs' (fe_extra cx ++ xs)) (mrestrict (w_H W) memc) (fe_sp0 cx) HE
    (fe_E_Ereg cx regs' xs) Hsv) as Hsv1.
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hsv1 c Hc) as Hck.
  unfold fe_sv_chunks in Hc. apply in_map_iff in Hc as (j & Ec & Hj). apply in_seq in Hj.
  apply (chunk_ok_mbyte _ (mrestrict (w_H W) memc)); [|exact Hck].
  intros i Hi. rewrite <- Ec in Hi |- *. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in Hi |- *.
  apply (s6_keep_stack lyc Sc Uc W memc mdc STKc (spZ regsc) FPc ly' S' U' W' mem' md' kc _ HARU HJc OK' PO');
    unfold LLVMF_STK in *; lia. }
(* the flag word at the new memory *)
assert (Hflag2 : rdword (aview tfibsegs (w_H W') mem') (fe_F cx + 56) = Some (fe_FL cx)).
{ apply (ACem.rdword_of_val_mem tfibsegs (w_H W') mem'); [|lia].
  intros j Hj.
  rewrite (s6_keep_frame cx lyc Sc Uc W memc mdc STKc (spZ regsc) FPc ly' S' U' W' mem' md' kc
    (fe_F cx + 56 + Z.of_nat j) HARU HJc OK' PO' Hin EF ltac:(lia)
    (HnF (fe_F cx + 56 + Z.of_nat j) ltac:(lia))).
  exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Hflag j Hj). }
apply (fe_canon B cx ly' S' U' W' mem' md' regs' xs r cs HARU' Hin2 ELY2).
- rewrite (fsw_pres regsc regs' 8%bv HP ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)). exact R8.
- rewrite (fsw_pres regsc regs' 24%bv HP ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)). exact R24.
- rewrite (fsw_pres regsc regs' 18%bv HP ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)). exact R18.
- rewrite (fsw_pres regsc regs' 25%bv HP ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)). exact R25.
- exact Hal16.
- unfold LLVMF_STK in *. lia.
- exact H47.
- intros a Ha. apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' a HARU'); [unfold LLVMF_STK in *; lia|].
  apply Hpres2. unfold LLVMF_STK in *. lia.
- exact Hsv2.
- exact Hflag2.
- exact Hwf.
- exact Hcin.
- exact Hcs.
Qed.



(* ---- the run between two boundaries writes only the frame, its shadow and the saved words ---- *)
Lemma s6_wr_out : forall cx E cs a,
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  in_wrange E (fe_regions cs) a ->
  fe_F cx <= a < fe_F cx + 64 \/ fe_SF cx <= a < fe_SF cx + 8 \/ fe_sp0 cx - 88 <= a < fe_sp0 cx.
Proof.
intros cx E cs a E8 E24 E25 (r & Hr & Ha). unfold fe_regions in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [fe_frame_region fe_shadow_region fs_ret_s0_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
- rewrite E24 in Ha. left. lia.
- rewrite E25 in Ha. right. left. lia.
- rewrite E8 in Ha. right. right. lia.
Qed.

(* an image byte is outside all three: a frame byte is no image byte (AR_client_img_law), the frame's shadow is
   above kLowMemEnd and the saved words above alloc_ceiling *)
Lemma s6_run_img : forall cx E lyc Sc Uc (W : world tfibsegs) mem mem' mdc cs a,
  ARU tfibsegs B lyc Sc Uc W mem mdc -> In (0, c_fpos cx) (frames Sc) -> frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  alloc_ceiling + LLVMF_STK <= fe_sp0 cx -> kLowMemEnd <= fe_SF cx ->
  frame_of E (fe_regions cs) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  in_img tfibsegs a ->
  mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros cx E lyc Sc Uc W mem mem' mdc cs a HARU Hin EF E8 E24 E25 Hsp Hsf HF Himg.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsk_segs_img a Himg) as Ha. unfold FS_IMG_END in Ha.
unfold mbyte. rewrite HF; [reflexivity|].
intros Hw. destruct (s6_wr_out cx E cs (bv_unsigned (Z_to_bv 64 a)) E8 E24 E25 Hw) as [Hr | [Hr | Hr]];
  rewrite (wz a ltac:(lia)) in Hr.
- apply (al_client_img _ _ LAWS lyc Sc W (unpoison Uc mem) mdc a (ARU_AR tfibsegs B lyc Sc Uc W mem mdc HARU));
    [right; left; exists 0, (c_fpos cx); rewrite EF; split; [exact Hin|]; cbn [fs_frame_bytes]; exact Hr | exact Himg].
- unfold kLowMemEnd in Hsf. lia.
- unfold LLVMF_STK in Hsp. lia.
Qed.

(* a byte of a live block is outside all three: blocks are disjoint from frames, lie in the application range (never in
   the shadow) and end below alloc_ceiling *)
Lemma s6_run_blk : forall cx E lyc Sc Uc (W : world tfibsegs) mem mem' mdc cs b m i,
  ARU tfibsegs B lyc Sc Uc W mem mdc -> In (0, c_fpos cx) (frames Sc) -> frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  alloc_ceiling + LLVMF_STK <= fe_sp0 cx -> kLowMemEnd <= fe_SF cx -> fe_SF cx + 8 <= kHighShadowEnd ->
  frame_of E (fe_regions cs) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  mbyte tfibsegs (mrestrict (w_H W) mem') (b + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (b + i).
Proof.
intros cx E lyc Sc Uc W mem mem' mdc cs b m i HARU Hin EF Hb Hi E8 E24 E25 Hsp Hsf1 Hsf2 HF.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W mem mdc HARU) as HAR.
destruct (al_blocks _ _ LAWS lyc Sc W (unpoison Uc mem) mdc b m HAR Hb) as (_ & H4096 & Hceilb & Happ & _).
pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W (unpoison Uc mem) mdc b m 0 (c_fpos cx) HAR Hb Hin) as Hd.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, Hfb in Hd.
unfold mbyte. rewrite HF; [reflexivity|].
assert (Hb64 : 0 <= b + i < 2 ^ 64) by lia.
unfold LLVMF_STK in Hsp. unfold kLowMemEnd in Hsf1. unfold kHighShadowEnd in Hsf2.
destruct Happ as (Hp0 & Hpl). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpl.
intros Hw. destruct (s6_wr_out cx E cs (bv_unsigned (Z_to_bv 64 (b + i))) E8 E24 E25 Hw) as [Hr | [Hr | Hr]];
  rewrite (wz (b + i) Hb64) in Hr; clear Hw.
- clear Hpl Hsf1 Hsf2 Hsp Hceilb. lia.
- clear Hd Hsp Hceilb. lia.
- clear Hd Hpl Hsf1 Hsf2. lia.
Qed.

(* fuzz/alloc.c's four statics are image bytes *)
Lemma s6_glob_keep : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HK (V1 & V2 & V3 & V4 & R).
assert (VM : forall g v, seg_covers g 8 = true -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hc Hv j Hj. rewrite (HK (g + Z.of_nat j) (seg_covers_img g 8 (g + Z.of_nat j) Hc ltac:(lia))).
  exact (Hv j Hj). }
split; [apply (VM G_LIVE live); [vm_compute; reflexivity | exact V1]|].
split; [apply (VM G_PEAK peak); [vm_compute; reflexivity | exact V2]|].
split; [apply (VM G_COUNT cnt); [vm_compute; reflexivity | exact V3]|].
split; [apply (VM G_FAIL fail); [vm_compute; reflexivity | exact V4] | exact R].
Qed.

(* ---- rebuilding the string and byte-window facts of a live block at a new state ---- *)
(* no user-poisoned shadow byte over an address no range of U covers *)
Lemma s6_ush_at : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> 0 <= x ->
  (forall r, In r U -> ~ (fst r <= x < fst r + snd r)) ->
  in_ush U (shadow_addr x) = false.
Proof.
intros ly S U W mem md x HARU Hx Hdis.
destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs).
destruct HARU as (_ & (OK & _) & _).
pose proof (proj1 (Forall_forall _ _) OK r Hr) as (A8 & L8 & M8 & _).
unfold shadow_addr in Hs.
apply Z.mod_divide in A8 as [a8 Ha8]; [|lia]. apply Z.mod_divide in M8 as [c8 Hc8]; [|lia].
rewrite Ha8, Hc8 in Hs. rewrite !Z.div_mul in Hs by lia.
pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
apply (Hdis r Hr). rewrite Ha8, Hc8. lia.
Qed.

(* cstr_ok carried to a new ARU state: the bytes by hypothesis, the shadow facts rebuilt from AR there *)
Lemma s6_cstr_carry : forall ly' S' U' (W' : world tfibsegs) mem' md' (W : world tfibsegs) mem b m p l,
  ARU tfibsegs B ly' S' U' W' mem' md' -> In (b, m) (ablocks B ly' S') -> 0 < m ->
  (forall r, In r U' -> fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 ->
     mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros ly' S' U' W' mem' md' W mem b m p l HARU Hb Hm Hdis Hbp Hbm HK
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & _ & _ & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly' S' U' W' mem' md' HARU) as HAR.
pose proof HARU as (_ & _ & PO).
destruct (al_blocks _ _ LAWS ly' S' W' (unpoison U' mem') md' b m HAR Hb) as (_ & Hb4096 & _ & _ & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hsh : forall x, p <= x < p + Z.of_nat (length l) + 1 -> in_ush U' (shadow_addr x) = false).
{ intros x Hx. apply (s6_ush_at ly' S' U' W' mem' md' x HARU ltac:(lia)).
  intros r Hr Hc. destruct (Hdis r Hr); lia. }
split; [split|].
- apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg).
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HK. lia.
- exact Hnz.
- split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
  split.
  { intros x Hx.
    destruct (range_addressable_of_block tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' b m p
      (Z.of_nat (length l) + 1) HAR Hb Hbp ltac:(lia) x Hx) as (v & Hv & Hok).
    exists v. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv |- *.
    rewrite <- (aview_unpoison_sh U' W' mem' (shadow_addr x)); [exact Hv | | exact (Hsh x ltac:(lia))].
    unfold shadow_addr, SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
    lia. }
  split.
  { destruct (al_shadow _ _ LAWS ly' S' W' (unpoison U' mem') md' b m HAR Hb) as (_ & Hhv').
    intros s Hs. apply (aview_unpoison_vis U' W' mem' s PO).
    apply (shadow_hull_vis_sub _ b (req_size m) p (Z.of_nat (length l) + 1) Hhv' Hbp ltac:(lia) ltac:(lia)).
    exact Hs. }
  intros a Ha. apply (aview_unpoison_vis U' W' mem' a PO).
  apply (block_word_tail_vis B ly' S' W' (unpoison U' mem') md' b m HAR Hb Hm).
  pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* src_rd of a byte window inside a live block, built from the bytes and AR *)
Lemma s6_src_blk : forall ly S U (W : world tfibsegs) mem md b m p l,
  ARU tfibsegs B ly S U W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  (forall r, In r U -> fst r + snd r <= p \/ p + Z.of_nat (length l) <= fst r) ->
  b <= p -> p + Z.of_nat (length l) <= b + m ->
  zbytes_at tfibsegs W mem p l ->
  src_rd tfibsegs W mem p l.
Proof.
intros ly S U W mem md b m p l HARU Hb Hm Hdis Hbp Hbm Hz.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & PO).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hb) as (_ & Hb4096 & Hbceil & Happ & _).
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hrq in Happ.
pose proof (fe_block_room B ly S W (unpoison U mem) md b m HAR Hb) as Hroom. rewrite Hrq in Hroom.
split; [exact Hz|]. split; [lia|]. split; [lia|].
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
split.
{ intros x Hx.
  destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md b m p
    (Z.of_nat (length l)) HAR Hb Hbp ltac:(lia) x Hx) as (v & Hv & Hok).
  exists v. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv |- *.
  rewrite <- (aview_unpoison_sh U W mem (shadow_addr x));
    [exact Hv | unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
     pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)); lia |].
  apply (s6_ush_at ly S U W mem md x HARU ltac:(lia)).
  intros r Hr Hc. destruct (Hdis r Hr); lia. }
intros Hpos s Hs. apply (aview_unpoison_vis U W mem s PO).
destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md b m HAR Hb) as (_ & Hhv').
apply (shadow_hull_vis_sub _ b (req_size m) p (Z.of_nat (length l)) Hhv' Hbp ltac:(rewrite Hrq; lia) ltac:(lia)).
exact Hs.
Qed.


(* ---- the parts of fe_common every boundary of the walk has from the journal alone ---- *)
Lemma s6_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha;
  [ apply (seg_covers_img 0xa3ca0 8 a ltac:(vm_compute; reflexivity))
  | apply (seg_covers_img 0x5da5c0 8 a ltac:(vm_compute; reflexivity))
  | apply (seg_covers_img 0x5da5e0 8 a ltac:(vm_compute; reflexivity))
  | apply (seg_covers_img 0x5da600 8 a ltac:(vm_compute; reflexivity)) ]; lia.
Qed.

Lemma s6_bb : forall ly3 S3 ly S l,
  Permutation (ablocks B ly3 S3) (l ++ ablocks B ly S) -> blocks_bytes S3 = bsum l + blocks_bytes S.
Proof.
intros ly3 S3 ly S l HP.
rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S).
rewrite (bsum_perm _ _ HP), bsum_app. reflexivity.
Qed.

(* the model's io, the payload's bytes and the live bytes at any boundary of the walk *)
Lemma s6_common : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 l KB,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  Permutation (ablocks B ly3 S3) (l ++ ablocks B (c_ly cx) (c_S cx)) ->
  0 <= k <= KB -> bsum l <= 2 ^ 32 ->
  fe_common cx k S3 W3 ms3 md3 KB.
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 l KB HB HJ HARU HP Hk Hl.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as ((HAP & _ & _ & _ & Hpay & _) & _).
pose proof HJ as (_ & _ & _ & _ & Hio & _ & _ & _ & _ & F2 & _).
split; [exact Hk|]. split.
{ apply (aos_step_closed_same_io FS_PSTAT_FP); [|exact Hio].
  apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
split; [|rewrite (s6_bb ly3 S3 (c_ly cx) (c_S cx) l HP); lia].
intros i Hi.
destruct Hpay as [[Hn0 _] | (Hn0 & Hinb)]; [lia|].
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hinb).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 (c_p cx) (c_n cx)
  (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) Hin3) as (_ & H4096 & Hbceil & Happ & _).
rewrite Hrq in Happ.
pose proof (in_app_addr (c_p cx) (c_n cx) (c_p cx + i) Happ ltac:(lia)) as Hap.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
rewrite (aview_at tfibsegs (w_H W3) (ms_mem ms3) (unpoison U3 (ms_mem ms3)) (c_p cx + i)).
2:{ symmetry. apply (FSW_strkit.unpoison_app B ly3 S3 U3 W3 (ms_mem ms3) md3 (c_p cx + i) HARU);
    unfold SHADOW_OFF in *; lia. }
apply (F2 (c_p cx) (c_n cx) i Hinb Hin3 ltac:(lia)).
intros Hf. exact (blk_img tfibsegs B LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 (c_p cx) (c_n cx) (c_p cx + i)
  (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU) Hin3 ltac:(lia) (s6_pstat_img (c_p cx + i) Hf)).
Qed.

(* the user-poisoned heads of the walk: at most the decoded block's *)
Lemma s6_heads_nil : forall ly S, fs_heads B ly S [].
Proof. intros ly S r Hr. destruct Hr. Qed.
Lemma s6_heads_one : forall ly S q n, In (q - HEAD, n + HEAD) (ablocks B ly S) -> 0 <= n ->
  fs_heads B ly S [(q - HEAD, HEAD)].
Proof.
intros ly S q n Hin Hn r [<-|[]]. cbn [fst snd]. split; [reflexivity|].
exists (n + HEAD). split; [exact Hin|]. unfold req_size, HEAD in *.
destruct (Z.eqb_spec (n + 16) 0); lia.
Qed.

(* a callee-saved register the walk left as its entry atom, read in the resumed env *)
Lemma s6_reg_keep : forall (E : env) ms (W : world tfibsegs) ss regs' xs (r : bv 5) (m nn : nat),
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn 0 ->
  aregs_preserved (ms_regs ms) regs' -> acallee_saved (Z.of_nat m) -> Z.of_nat m = bv_unsigned r ->
  ew (Ereg regs' xs) m = ew E nn.
Proof.
intros E ms W ss regs' xs r m nn HS Hr HP Hcs Hm.
rewrite (ew_Ereg_nat regs' xs m r Hm), (fsw_pres (ms_regs ms) regs' r HP ltac:(rewrite <- Hm; exact Hcs)).
exact (s6_reg_at E ss ms W r nn HS Hr).
Qed.

(* the canonical registers across a program call *)
Lemma s6_core_keep : forall cx E ms (W : world tfibsegs) ss regs' xs,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> fe_regs_core cx E ->
  aregs_preserved (ms_regs ms) regs' ->
  sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 18%bv = SOff 18 0 ->
  sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
  sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
  fe_regs_core cx (Ereg regs' xs).
Proof.
intros cx E ms W ss regs' xs HS (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27) HP
  R8 R9 R2 R18 R24 R25 R3 R4 R26 R27.
split; [rewrite (s6_reg_keep E ms W ss regs' xs 8%bv 8 8 HS R8 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A8|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 9%bv 9 9 HS R9 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A9|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 2%bv 2 2 HS R2 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A2|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 18%bv 18 18 HS R18 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A18|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 24%bv 24 24 HS R24 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A24|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 25%bv 25 25 HS R25 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A25|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 3%bv 3 3 HS R3 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A3|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 4%bv 4 4 HS R4 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A4|].
split; [rewrite (s6_reg_keep E ms W ss regs' xs 26%bv 26 26 HS R26 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A26|].
rewrite (s6_reg_keep E ms W ss regs' xs 27%bv 27 27 HS R27 HP ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact A27.
Qed.

(* what the entry facts give about the payload and the text *)
Lemma s6_zfind_lt : forall c l j, zfind c l = Some j -> (j < length l)%nat.
Proof.
intros c l. induction l as [|x t IH]; intros j H; [discriminate H|].
cbn [zfind length] in H |- *. destruct (x =? c); [injection H as <-; lia|].
destruct (zfind c t) as [j'|] eqn:E; [|discriminate H]. cbn in H. injection H as <-.
pose proof (IH j' eq_refl). lia.
Qed.

Lemma s6_entry : forall cx, fe_base B cx ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) /\ YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) /\
  raZ (c_regs cx) = RA_LLVMF /\ frames (c_S cx) = [] /\
  st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + ACfn.LIVE_LIB <= LIVE_MAX /\
  0 <= c_n cx /\ Z.of_nat (length (fe_tb cx)) = fe_n cx /\ 0 <= fe_n cx /\
  WriterSpec.bytes_ok (fe_tb cx) /\
  fs_stat tfibsegs (c_W cx) (c_mem cx) (c_live cx) (c_cnt cx) /\
  0 <= c_cnt cx /\ c_cnt cx + FS_CNT_LIB < 2 ^ 63 /\ c_live cx + ACfn.LIVE_LIB < 2 ^ 64.
Proof.
intros cx ((HAP & Hra0 & _ & _ & Hpay & Hlen & _ & Hfr0 & Hev & Hlive & _) & Hstat & Hc0 & Hcnt & Hlv).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
assert (Hn0 : 0 <= c_n cx) by (destruct Hpay as [[-> _] | (H & _)]; lia).
assert (Hbl : length (fe_bytes cx) = length (c_pl cx)) by (unfold fe_bytes; apply length_map).
assert (Hfn : 0 <= fe_n cx /\ (Z.to_nat (fe_n cx) <= length (fe_bytes cx))%nat).
{ unfold fe_n. destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:E.
  - pose proof (s6_zfind_lt 0 (fe_bytes cx) j E). split; lia.
  - rewrite Hbl. split; [lia|]. rewrite Hlen in *. lia. }
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hra0|]. split; [exact Hfr0|].
split; [exact Hev|]. split; [exact Hlive|]. split; [exact Hn0|].
split; [unfold fe_tb; rewrite length_firstn; lia|]. split; [lia|].
split.
{ apply Forall_forall. intros x Hx.
  assert (Hin : In x (fe_bytes cx))
    by (rewrite <- (firstn_skipn (Z.to_nat (fe_n cx)) (fe_bytes cx)); apply in_or_app; left; exact Hx).
  unfold fe_bytes in Hin. apply in_map_iff in Hin as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
split; [exact Hstat|]. split; [exact Hc0|]. split; [exact Hcnt | exact Hlv].
Qed.

(* a word on the real stack reads the same on the machine's memory and on its unpoisoned reading *)
Lemma s6_rdword_unpoison : forall ly S U (W : world tfibsegs) mem md a v,
  ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) mem) a = Some v ->
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) a = Some v.
Proof.
intros ly S U W mem md a v HARU H1 H2 H.
unfold rdword in H |- *.
rewrite (fsw_aview_unpoison_high B ly S U W mem md a HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 1) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 2) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 3) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 4) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 5) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 6) HARU ltac:(lia)),
        (fsw_aview_unpoison_high B ly S U W mem md (a + 7) HARU ltac:(lia)).
exact H.
Qed.

(* the walk's footprint misses the entry's fake frame and every live block: both are client memory, the statics are
   image bytes *)
Lemma s6_frame_not_pstat : forall cx lyc Sc Uc (W : world tfibsegs) mem md,
  ARU tfibsegs B lyc Sc Uc W mem md -> In (0, c_fpos cx) (frames Sc) -> frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  forall a, fe_F cx <= a < fe_F cx + 64 -> ~ inFP FS_PSTAT_FP a.
Proof.
intros cx lyc Sc Uc W mem md HARU Hin EF a Ha Hf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply (al_client_img _ _ LAWS lyc Sc W (unpoison Uc mem) md a (ARU_AR tfibsegs B lyc Sc Uc W mem md HARU));
  [right; left; exists 0, (c_fpos cx); rewrite EF; split; [exact Hin|]; cbn [fs_frame_bytes]; exact Ha
  | exact (s6_pstat_img a Hf)].
Qed.
Lemma s6_blk_not_pstat : forall lyc Sc Uc (W : world tfibsegs) mem md b m i,
  ARU tfibsegs B lyc Sc Uc W mem md -> In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  ~ inFP FS_PSTAT_FP (b + i).
Proof.
intros lyc Sc Uc W mem md b m i HARU Hb Hi Hf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
exact (blk_img tfibsegs B LAWS lyc Sc W (unpoison Uc mem) md b m (b + i)
  (ARU_AR tfibsegs B lyc Sc Uc W mem md HARU) Hb ltac:(lia) (s6_pstat_img (b + i) Hf)).
Qed.
Lemma s6_pstat_sub : forall cx ly S lyc Sc,
  fsw_fp_sub B ly S lyc Sc [(0, c_fpos cx)] FS_PSTAT_FP FS_PSTAT_FP.
Proof. intros cx ly S lyc Sc a Hf. right. right. left. split; [exact Hf | exact (s6_pstat_img a Hf)]. Qed.

(* inFP of an appended footprint *)
Lemma s6_inFP_app : forall F1 F2 a, inFP (F1 ++ F2) a -> inFP F1 a \/ inFP F2 a.
Proof.
intros F1 F2 a (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr];
  [left | right]; exists r; split; assumption.
Qed.
(* the decode call's footprint: the statics (image arm) and the entry's own `len` slot (own-frame arm) *)
Lemma s6_dec_sub : forall cx ly S lyc Sc lenp,
  frame_addr lyc 0 (c_fpos cx) = fe_F cx -> fe_F cx <= lenp -> lenp + 8 <= fe_F cx + 64 ->
  fsw_fp_sub B ly S lyc Sc [(0, c_fpos cx)] FS_PSTAT_FP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]).
Proof.
intros cx ly S lyc Sc lenp EF H1 H2 a Hf.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (s6_inFP_app _ _ a Hf) as [Hp | Hl].
- right. right. left. split; [exact Hp | exact (s6_pstat_img a Hp)].
- right. right. right. left. destruct Hl as (r & [<-|[]] & Ha). cbn [fst snd] in Ha.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite EF, Hfb. lia.
Qed.
(* and it misses the flag word at the top of the frame *)
Lemma s6_dec_flag : forall cx lyc Sc Uc (W : world tfibsegs) mem md lenp,
  ARU tfibsegs B lyc Sc Uc W mem md -> In (0, c_fpos cx) (frames Sc) -> frame_addr lyc 0 (c_fpos cx) = fe_F cx ->
  lenp + 8 <= fe_F cx + 56 ->
  forall a, fe_F cx + 56 <= a < fe_F cx + 64 -> ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a.
Proof.
intros cx lyc Sc Uc W mem md lenp HARU Hin EF Hlen a Ha Hf.
destruct (s6_inFP_app _ _ a Hf) as [Hp | Hl].
- exact (s6_frame_not_pstat cx lyc Sc Uc W mem md HARU Hin EF a ltac:(lia) Hp).
- destruct Hl as (r & [<-|[]] & Har). cbn [fst snd] in Har. lia.
Qed.

(* a subtraction the engine left symbolic: a0 - s7 at 0x810ac *)
Lemma s6_denot_sub : forall E n m x y,
  ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= y <= x -> x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit (-1)))) = Z_to_bv 64 (x - y).
Proof.
intros E n m x y Hn Hm Hyx Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n x Hn ltac:(lia)), (U_atom E m y Hm ltac:(lia)), U_SLit.
assert (HM : M64 = 2 ^ 64) by reflexivity.
unfold zcanon. rewrite HM. change (-1 mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite Zplus_mod_idemp_r.
replace (x + y * (2 ^ 64 - 1)) with (x - y + y * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

End s6a.
