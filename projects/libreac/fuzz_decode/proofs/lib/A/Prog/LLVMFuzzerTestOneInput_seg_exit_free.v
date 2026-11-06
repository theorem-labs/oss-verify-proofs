(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module names changed; 614 of its 669 lines of code are new or changed and 2634 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_free: ex_free_ok, the fifth piece of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v, ex_free_stmt),
   offsets +0x98c .. +0x9a4 of the audited listing lib/A/Prog/DecodeList.v (lines 639-645), from ex_st_98c to
   llvm_a_st_9a8.

   What the code does:
     +0x98c  mv a0, s7                            the upstream buffer upb
     +0x990  jal __interceptor_trampoline_free    free #2, returns to +0x994
     +0x994  mv a0, s4                            the copy of the payload, res
     +0x998  jal __interceptor_trampoline_free    free #3, returns to +0x99c
     +0x99c  li a0, -8
     +0x9a0  sb a0, 4(s11)                        the local's two shadow bytes back to 0xf8 (DEC_SH_MID)
     +0x9a4  sb a0, 5(s11)
   and +0x9a8 is the join llvm_a_st_9a8 the tail piece starts from.

   Shape of the proof, following the Qed walks of the same engine in this unit (a Theorem Labs lane's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v for the seat / saved words / call idiom and a Theorem Labs lane's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_crt.v for the cut-point rebuild after a call):
   - three short runs, each seated FRESH on the state the previous step left;
   - the two calls by lib/A/Prog/YC85.v afree04_sub at the statement's afree04_rule premise, with the frame-pointer
     chain pushed from the entry's achain (lib/Reusable/YCbq.v achain_push / achain_chain_pre) and the allocator
     trace of dec_llvmf_utraces;
   - the two shadow stores on the PLAIN pi engine (lib/A/Prog/PaSym.v sym_run_to_pi, journal step
     lib/Reusable/YCbq.v SRr_chain_AJ): the token executor refuses a writable region inside the shadow band
     (lib/Reusable/YCbn.v:116 cells_safe_b), measured by a Theorem Labs lane. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  DecodeSyms DecodeList DecodeAddr DecodePa DecodePaLib DecodeImg YC4b YC1g YC1h YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. Generic helpers                                                   *)
(* ------------------------------------------------------------------ *)

Section mh. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := decodesegs0.
(* a Theorem Labs lane's seg_entry.v rdword_kept / garr8_kept (a Theorem Labs lane's crt piece has the same two). *)
Lemma xf_rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma xf_garr8_kept : forall H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG. apply (garr8_frame segs _ _ _ _ HG). intros a Ha.
apply (mbyte_of_aview segs). replace a with (base + (a - base)) by lia. apply HK. lia.
Qed.
Lemma xf_saved_at_range : forall o, In o dec_a_saved_at -> 8 <= fst o <= 104.
Proof. intros o Ho. unfold dec_a_saved_at in Ho. repeat (destruct Ho as [<-|Ho]; [cbn; lia|]). destruct Ho. Qed.
(* The blocks of one state are pairwise disjoint (AR_sep_law), so no block is listed twice. *)
Lemma xf_pw_nodup : forall l : list (Z * Z), Forall (fun b : Z * Z => 0 <= snd b) l ->
  pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
intros l. induction l as [|x l IH]; intros HF HP; [apply List.NoDup_nil|].
cbn [map] in HP. destruct HP as [HFa HP]. inversion HF as [|x0 l0 Hx HFl]; subst.
apply List.NoDup_cons; [|exact (IH HFl HP)].
intros Hin.
pose proof (proj1 (Forall_forall _ _) HFa (fst x, req_size (snd x))
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l x Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos (snd x) Hx) as [H1 _]. lia.
Qed.
(* call_trace0 of YG0d is check_round_trip_cg's dec_utrace at the chain's return addresses. *)
Lemma xf_flat : forall pc0 ch,
  flat_map (fun r : Z * Z * Z => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch =
  flat_map (fun ra : Z => if ra =? pc0 then [] else [ra]) (spine ch).
Proof.
intros pc0 ch. induction ch as [|[[fp ra] v] ch IH]; cbn [flat_map spine map]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
Lemma xf_trace : forall pc0 regs ch, call_trace0 pc0 regs ch = dec_utrace pc0 (raZ regs :: spine ch).
Proof.
intros pc0 regs ch. unfold call_trace0, unwind_of_chain, dec_utrace.
cbn [flat_map]. rewrite xf_flat. reflexivity.
Qed.
End mh.

(* The value of register r in the machine state of a symbolic state HS (a Theorem Labs lane's reg_at). *)
Ltac reg_at HS r v H tac :=
  lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* 2. The seats and the plain-pi run                                    *)
(* ------------------------------------------------------------------ *)

(* The first two seats hold no region (the two stretches only move a register and call); the third holds the frame's
   eight shadow bytes through s11 (atom 27), writable at 4 .. 5, which is what the two sb write. *)
Definition xf_ss1 : sstate := mkSS 0x98c sr_atoms [] None (mkFacts [] [] []).
Definition xf_ss2 : sstate := mkSS 0x994 sr_atoms [] None (mkFacts [] [] []).
Definition xf_rsh : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 4 6 [].
Definition xf_ss3 : sstate := mkSS 0x99c sr_atoms [xf_rsh] None (mkFacts [] [] []).
Definition XF_FUEL : N := 32.
Definition xf_ss3_end : sstate := Eval vm_compute in fst (sym_run_toN_pi decode_tpi XF_FUEL 0x9a8 xf_ss3).
Definition xf_st3_end : prun_status dsym := Eval vm_compute in snd (sym_run_toN_pi decode_tpi XF_FUEL 0x9a8 xf_ss3).
Lemma xf_run3_eq : sym_run_toN_pi decode_tpi XF_FUEL 0x9a8 xf_ss3 = (xf_ss3_end, xf_st3_end).
Proof. vm_compute. reflexivity. Qed.
Lemma xf_run3_pc : ss_pc xf_ss3_end = 0x9a8.
Proof. reflexivity. Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := decodesegs0.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
(* The env of a seat: the registers as atoms 0 .. 31, no extra atom (s11 itself carries the shadow address). *)
Definition xf_E (regs : bvmap 5 word) : env := Eimg (PI := PI_decode) (Ereg regs []).
Lemma xf_E_img : forall regs, img_env VAL A_LIM (xf_E regs).
Proof. intros regs. unfold xf_E. apply Eimg_env. Qed.
Lemma xf_E_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (xf_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold xf_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma xf_E_agree : forall regs, env_agree 32 (Ereg regs []) (xf_E regs).
Proof.
intros regs. split; [|reflexivity].
intros n Hn. unfold xf_E. first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia.
Qed.
Lemma xf_seat0 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z),
  st_ok_pi SEGS VAL (xf_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- unfold xf_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
Qed.
(* The third seat: the frame's shadow bytes, writable at 4 .. 5. *)
Lemma xf_seat3 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (sh : Z),
  YK11.getr regs 27 = w64 sh -> SHADOW_OFF <= sh -> sh + 8 <= kHighMemBeg ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) mem (sh + i)) ->
  st_ok_pi SEGS VAL (xf_E regs) xf_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x99c)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem sh R27 Hlo Hhi Hpres.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U27 : bv_unsigned (ew (xf_E regs) 27) = sh).
{ rewrite (xf_E_reg regs 27 27%bv eq_refl), R27. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF in Hlo. lia. }
rewrite restrict_mkst_fx. unfold xf_ss3.
apply pa_entry_st_ok_full.
- unfold xf_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold xf_rsh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U27. split; [unfold SHADOW_OFF in Hlo; lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
Qed.
(* A one-byte chunk of a region read back as a view byte. *)
Lemma xf_chunk_aview : forall E (H : word -> bool) (m : word -> option byte) base n lo hi wlo whi cs off (e : sv),
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = base -> In (YP09.mkChunk off (CVal 1 e)) cs ->
  aview SEGS H m (base + off) = Some (bv_unsigned (byte_of_word (sv_denot E e) 0)).
Proof.
intros E H m base n lo hi wlo whi cs off e HR Hb Hin.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hcb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hcb. injection Hcb as <-.
rewrite Z.add_0_r in Hm. unfold aview. cbn [YP09.c_off] in Hm. rewrite Hm. reflexivity.
Qed.
End en.

(* The plain pi engine with the caller's journal: lib/Reusable/YCbq.v SRr_chain_AJ on PaRun's sym_run_to_pi_sound,
   the form a Theorem Labs lane's tail piece uses for its shadow stores. *)
Section rw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Definition xf_plain_stop (st : prun_status dsym) : Prop :=
  match st with PRS_running | PRS_stopped _ => True | _ => False end.
Lemma xf_run_pi_AJ : forall (B : asyms), AR_laws SEGS B ->
  forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi decode_tpi n stop ss = (ss', st) -> xf_plain_stop st ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
     st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros B LAWS W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_run_toN_pi, decode_tpi in Hrun.
destruct (sym_run_to_pi_sound dsym SEGS (clookup (@pa_tbl _ decode_listing PI_decode)) VAL
  (@pa_sigma _ decode_listing PI_decode) decode_listing (pa_fetch_ok (PI := PI_decode))
  (@pa_cert _ decode_listing PI_decode) (@pa_B_ok _ decode_listing PI_decode) A_LIM A_LIM_text
  (@pl_lim decode_listing PL_decode)
  _ stop E ss ss' st _ HE HS Hrun) as (msr' & Hms & HS'0 & _ & Hfr0).
assert (HS' : st_ok_pi SEGS VAL E ss' msr')
  by (destruct st; cbn [prun_post] in HS'0; first [exact HS'0 | destruct Hst]).
assert (Hfr : frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr'))
  by (first [exact Hfr0 | destruct ss; exact Hfr0]).
eapply (SRr_chain_AJ SEGS B LAWS decode_segs_low decode_wx W E ss (abs_ss VAL ss') ms msr'
  STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q Hms HS' Hfr HJ Hwr).
intros ms' mat' HSe HJe Hfe Hfe2 Hge. apply (Hk ms' mat' HSe HJe Hfe2).
Qed.
End rw.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section exfree. Context {rc : YM05.RunCeil}.
(* The Variables of LLVMFuzzerTestOneInput_seg_exit_cuts.v's Section cuts, in its order. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).

Theorem ex_free_ok :
  ex_free_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_free_stmt.
intros HPCF HUT LAWS ML MTL AFREE cx W' c' HB HROMv HST.
pose proof HB as HB0.
unfold dec_a_base, dec_lib_pre_x in HB.
pose proof (proj1 HB) as HAFN.
pose proof HB as HBr. apply proj2 in HBr. pose proof (proj1 HBr) as HraE. apply proj2 in HBr.
apply proj2 in HBr. apply proj2 in HBr. pose proof (proj1 HBr) as Hpn. apply proj2 in HBr.
pose proof (proj1 HBr) as Hplen. apply proj2 in HBr.
pose proof (proj1 HBr) as Hgarr0. apply proj2 in HBr.
pose proof (proj1 HBr) as Hfrs0. apply proj2 in HBr.
pose proof (proj1 HBr) as Hnev0. apply proj2 in HBr.
pose proof (proj1 HBr) as Hbb0.
pose proof HAFN as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H47 & Hbot0 & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : DEC_LLVMF_STK = 32768) by reflexivity.
assert (HSP0c : alloc_ceiling + 32768 <= d_sp0 cx) by (unfold d_sp0 in *; lia).
destruct HST as (fx' & ly1 & S1 & regs1 & mem1 & md1 & k & res & upb & E0 & Hfrm1 & HCORE & Hkle & HPERM
  & Hres4 & Hupb4 & HMLE & HMOK & HFR & R20 & R23 & HFSH).
pose proof HCORE as (HJ1 & HFRS1 & R8 & R9 & HSP & HSPR & HSP32 & RGP & RTP & HSAVED & HF4096 & HFmod
  & HFPRES & HFLW & HPAY & HGARR).
pose proof HFR as (RS3 & RS5 & RS11).
pose proof HFSH as (HSHL & HSH4 & HSH5 & HSHR).
(* ---- arithmetic of the two stack pointers and the frame ---- *)
assert (HASv : ASTACK = 16384) by reflexivity.
assert (HSP116 : d_sp1 cx mod 16 = 0) by lia.
assert (HSP016 : d_sp0 cx mod 16 = 0) by (unfold d_sp0; exact Hsp16).
assert (HSP08 : d_sp0 cx mod 8 = 0) by lia.
assert (HSP1c : alloc_ceiling <= d_sp1 cx) by lia.
assert (HSP0u : 0 <= d_sp0 cx < 2 ^ 64) by (unfold d_sp0 in *; lia).
assert (HTOP64 : ly_top (d_ly cx) <= 2 ^ 64) by lia.
assert (HinF1 : List.In (DEC_FCLASS, d_fpos cx) (frames S1)) by (rewrite HFRS1; left; reflexivity).
destruct (frames_bounds segs B LAWS ly1 S1 W' mem1 md1 DEC_FCLASS (d_fpos cx) (proj1 HJ1) HinF1)
  as (HFb4096 & HFceil & _).
assert (HFaddr1 : frame_addr ly1 DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. pose proof HJ1 as (_ & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite HFaddr1 in HFceil. change (fs_frame_bytes DEC_FCLASS) with 64 in HFceil.
assert (HSHlo : SHADOW_OFF <= d_SH cx) by (unfold d_SH, shadow_addr; lia).
assert (HSHhi : d_SH cx + 8 <= kHighMemBeg)
  by (unfold d_SH, shadow_addr, SHADOW_OFF; rewrite C3; lia).
assert (HSHu : 0 <= d_SH cx < 2 ^ 64) by (unfold SHADOW_OFF in HSHlo; lia).
(* ---- the blocks of the cut state are distinct ---- *)
assert (HND : List.NoDup (ablocks B ly1 S1)).
{ apply xf_pw_nodup.
  - apply Forall_forall. intros [b m] Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m (proj1 HJ1) Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
  - destruct (al_sep _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Hpw & _).
    exact (proj1 (pairwise_app_l _ _ _ Hpw)). }
pose proof (Permutation_NoDup HPERM HND) as HND2.
unfold ex_blocks in HND2. cbn [app] in HND2.
assert (HnotR : ~ List.In (res, dec_a_len (d_n cx)) (ablocks B (d_ly cx) (d_S cx)) /\
                (res, dec_a_len (d_n cx)) <> (upb, ex_uolen cx)).
{ pose proof (NoDup_remove_2 _ _ _ HND2) as Hx. split; [intros Hin; apply Hx, in_or_app; left; exact Hin|].
  intros Heq. apply Hx, in_or_app; right. left. symmetry. exact Heq. }
destruct HnotR as (HnotR & HRU).
assert (HnotU : ~ List.In (upb, ex_uolen cx) (ablocks B (d_ly cx) (d_S cx))).
{ pose proof (NoDup_remove_1 _ _ _ HND2) as Hx. pose proof (NoDup_remove_2 _ _ _ Hx) as Hy.
  intros Hin. apply Hy, in_or_app; left; exact Hin. }
assert (HinU : List.In (upb, ex_uolen cx) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app; right. right. left. reflexivity. }
assert (HinR1 : List.In (res, dec_a_len (d_n cx)) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app; right. left. reflexivity. }
(* ---- the chain and the trace of a free call ---- *)
assert (CHAIN : forall (W2 : world segs) (mem2 : word -> option byte) ly2 S2 md2 kk (regsT : bvmap 5 word),
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 kk ->
  dec_a_saved cx (aview segs (w_H W2) mem2) ->
  YK11.getr regsT 8 = w64 (d_sp0 cx) -> spZ regsT = d_sp1 cx -> 4096 <= raZ regsT ->
  exists ch, chain_pre ly2 (aview segs (w_H W2) mem2) regsT ch /\ List.In (spine ch) [[]; [RA_LLVMF]]).
{ intros W2 mem2 ly2 S2 md2 kk regsT HJx HSVx Rs0 Rsp Rra.
  pose proof HJx as (HARx & Hlyx & _ & _ & _ & _ & _ & _ & F1x & _).
  assert (Etop : ly_top ly2 = ly_top (d_ly cx))
    by (destruct Hlyx as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  assert (Hs0v : s0Z regsT = d_sp0 cx)
    by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small; lia).
  unfold dec_a_saved, dec_a_saved_at in HSVx.
  pose proof (proj1 (Forall_forall _ _) HSVx (8, 1) ltac:(cbn; tauto)) as Hw8.
  pose proof (proj1 (Forall_forall _ _) HSVx (16, 8) ltac:(cbn; tauto)) as Hw16.
  cbn [fst snd] in Hw8, Hw16.
  destruct (Z_lt_le_dec (d_sp0 cx) (ly_top (d_ly cx) - 16)) as [Hlt | Hge].
  - exists [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))].
    split; [| rewrite HraE; cbn [spine map fst snd]; right; left; reflexivity].
    eapply (achain_chain_pre ly2 (aview segs (w_H W2) mem2) (d_sp1 cx) (d_sp0 cx) _ regsT);
      [| lia | exact Hs0v | exact Rra].
    apply (achain_ly_top (d_ly cx) ly2 _ _ _ _ Etop).
    eapply (achain_push (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (aview segs (w_H W2) mem2)
      (d_sp0 cx) (s0Z (d_regs cx)) (raZ (d_regs cx)) [] (d_sp1 cx) Hch0 HTOP64);
      [ intros a Ha; apply F1x; lia | exact Hw8 | exact Hw16 | exact Hra40 | lia | exact HSP08 | lia | lia ].
  - exists []. split; [| left; reflexivity].
    eapply (achain_chain_pre ly2 (aview segs (w_H W2) mem2) (d_sp1 cx) (d_sp0 cx) [] regsT);
      [| lia | exact Hs0v | exact Rra].
    left. split; [right; left; lia | reflexivity]. }
assert (HTRACE : forall (regsT : bvmap 5 word) ch, List.In (spine ch) [[]; [RA_LLVMF]] ->
  List.In (raZ regsT) DEC_LLVMF_RA_FREE ->
  List.In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B)).
{ intros regsT ch Hsp Hra. rewrite xf_trace. destruct (HUT (spine ch) Hsp) as (_ & Hfree). apply Hfree. exact Hra. }
(* ---- what one free keeps: the saved words, the frame with its shadow, and every other block ---- *)
assert (KEEP : forall (Wb Wa : world segs) (mb ma : word -> option byte) ly2 S2 mdb (pa nn : Z),
  AR segs B ly2 S2 Wb mb mdb ->
  List.In (pa, nn) (ablocks B ly2 S2) ->
  frames S2 = [(DEC_FCLASS, d_fpos cx)] ->
  frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx ->
  acall_kept segs B ly2 S2 Wb mb Wa ma (d_sp1 cx - ASTACK) (d_sp1 cx) (fun a => pa <= a < pa + req_size nn) ->
  (forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H Wa) ma a = aview segs (w_H Wb) mb a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H Wa) ma a = aview segs (w_H Wb) mb a) /\
  (forall i, 0 <= i < 8 -> aview segs (w_H Wa) ma (d_SH cx + i) = aview segs (w_H Wb) mb (d_SH cx + i)) /\
  (forall b m i, List.In (b, m) (ablocks B ly2 S2) -> (b, m) <> (pa, nn) -> 0 <= i < req_size m ->
     aview segs (w_H Wa) ma (b + i) = aview segs (w_H Wb) mb (b + i))).
{ intros Wb Wa mb ma ly2 S2 mdb pa nn HARb Hinb Hfrsb HF2 HK.
  pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (Hfin : List.In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfrsb; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pa nn HARb Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
  pose proof (req_size_pos nn ltac:(lia)) as (Hrq1 & Hrq2).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ pa nn DEC_FCLASS (d_fpos cx) HARb Hinb Hfin) as Hdf.
  unfold zdisjoint, frame_rng in Hdf. cbn [fst snd] in Hdf. rewrite HF2 in Hdf.
  change (fs_frame_bytes DEC_FCLASS) with 64 in Hdf.
  unfold in_app in Hbapp.
  assert (HLSB : kLowShadowBeg < SHADOW_OFF) by (unfold kLowShadowBeg, SHADOW_OFF; lia).
  unfold ASAN_CEIL in Hbapp.
  split; [|split; [|split]].
  - intros a Ha. apply K1; lia.
  - intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF2. change (fs_frame_bytes DEC_FCLASS) with 64. lia.
    + cbn beta. lia.
  - intros i Hi. apply (K4 DEC_FCLASS (d_fpos cx) (d_SH cx + i) Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite HF2. change (fs_frame_bytes DEC_FCLASS / 8) with 8.
      unfold d_SH. lia.
    + cbn beta. lia.
  - intros b m i Hin2 Hne Hi. apply (K2 b m i Hin2 Hi).
    pose proof (sep_blocks segs B LAWS _ _ _ _ _ b m pa nn HARb Hin2 Hinb Hne) as Hd2.
    unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. cbn beta. lia. }
(* ---- +0x98c .. +0x990: mv a0,s7 and the jal into the free wrapper ---- *)
assert (HBASEeq : DEC_A_LLVMF = BASE) by (vm_compute; reflexivity).
assert (HBASEb : 4096 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64)
  by (split; [vm_compute; discriminate | vm_compute; reflexivity]).
assert (Hpcw : forall o : Z, w64 (DEC_A_LLVMF + o) = Z_to_bv 64 (BASE + o))
  by (intros o; unfold w64; rewrite HBASEeq; reflexivity).
subst c'. rewrite (Hpcw 0x98c).
pose proof (@paj_run fx' rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS) as RUN.
pose proof (xf_E_img regs1) as HEIa.
pose proof (xf_seat0 (fx := fx') W' regs1 mem1 0x98c) as HSa.
change (mkSS 0x98c sr_atoms [] None (mkFacts [] [] [])) with xf_ss1 in HSa.
assert (SHOKa : sh_ok SEGS (SOff 32 0) (@nil shent) (xf_E regs1) (mrestrict (w_H W') mem1)) by constructor.
pose proof HJ1 as HJa.
paj_run_tok RUN HSa HJa SHOKa Bspan; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdA := mdx) in *; clearbody mdA end.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem1 a).
{ intros a Ha.
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
    refine (kept_of_frame Ex rsx Hh m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    let wsv := eval vm_compute in (windows rsx) in change (windows rsx) with wsv end.
  intros bb wlo whi x Hin Hr. cbn [In] in Hin. destruct Hin. }
pose proof (xf_E_agree regs1) as HAEa.
assert (HPRa : aregs_preserved regs1 (ms_regs ms))
  by (eapply aregs_preserved_of_st_ok; [exact HSa | exact HAEa | vm_compute; reflexivity]).
reg_at HSa (10%bv : bv 5) (w64 upb) Qa0
  ltac:(cbn [sv_denot]; rewrite (xf_E_reg regs1 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
reg_at HSa (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x994)) Qra ltac:(apply codeptr_val; exact HEIa).
assert (Qsp : spZ (ms_regs ms) = d_sp1 cx)
  by (unfold spZ; rewrite <- HSP; unfold spZ; f_equal; exact (HPRa 2 ltac:(unfold acallee_saved; lia))).
assert (Qgp : YK11.getr (ms_regs ms) 3 = w64 (as_gp B))
  by (transitivity (YK11.getr regs1 3); [exact (HPRa 3 ltac:(unfold acallee_saved; lia)) | exact RGP]).
assert (Qtp : YK11.getr (ms_regs ms) 4 = w64 (as_tp B))
  by (transitivity (YK11.getr regs1 4); [exact (HPRa 4 ltac:(unfold acallee_saved; lia)) | exact RTP]).
assert (Qs0 : YK11.getr (ms_regs ms) 8 = w64 (d_sp0 cx))
  by (transitivity (YK11.getr regs1 8); [exact (HPRa 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Qraz : raZ (ms_regs ms) = DEC_A_LLVMF + 0x994)
  by (unfold raZ; rewrite Qra, unsigned_lit_small by lia; rewrite HBASEeq; reflexivity).
assert (HNEV1 : st_nev S1 < EV_MAX).
{ pose proof HJ1 as (_ & _ & _ & _ & _ & _ & Hn1 & _).
  unfold dec_ev_86c, DEC_CRT_EV in Hkle. unfold DEC_EV_LIB in Hnev0. lia. }
destruct (CHAIN W' (ms_mem ms) ly1 S1 mdA k (ms_regs ms) HJa
  ltac:(unfold dec_a_saved; apply Forall_forall; intros o Ho;
        pose proof (xf_saved_at_range o Ho) as Hor;
        rewrite (xf_rdword_kept (aview segs (w_H W') mem1)) by (intros i Hi; apply KR1; lia);
        exact (proj1 (Forall_forall _ _) HSAVED o Ho))
  Qs0 Qsp ltac:(rewrite Qraz; unfold DEC_A_LLVMF, AF_LLVMFuzzerTestOneInput, decode_text; lia))
  as (ch1 & Hch1 & Hspine1).
pose proof (proj1 HJa) as HARa.
pmkst HSa.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS___interceptor_trampoline_free)) mm rom) mdx) Q)
end.
rewrite <- HPCF.
eapply SRr_bind.
{ eapply (afree04_sub segs B LAWS decode_segs_low MT (AFREE fx') W' (ms_regs ms) (ms_mem ms)
    DEC_LLVMF_STK (d_sp0 cx) (@nil (Z * Z)) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly1 S1 mdA k upb (ex_uolen cx) (d_sp1 cx - d_sp0 cx)
    (Z_to_bv 64 (BASE + 0x994)) ch1 HJa HinU Qa0);
  [ lia | lia | lia | lia | exact Qgp | exact Qtp | exact Qra
  | apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity]
  | exact HNEV1 | exact Hch1
  | apply HTRACE; [exact Hspine1 | rewrite Qraz; unfold DEC_LLVMF_RA_FREE; cbn [map List.In]; right; left; reflexivity]
  | intros Hbad; exfalso; exact (HnotU Hbad)
  | apply (mo_ok_le MT MTL S1 (mo_free MT) (mo_free MT + mo_free MT) HMOK);
    pose proof (mo_free_nonneg MT MTL); lia ]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfrs2 & HK1
  & MLE1 & _).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx) - ASTACK) with (d_sp1 cx - ASTACK) in HK1 by lia.
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK1 by lia.
destruct (KEEP W' W2 (ms_mem ms) mem2 ly1 S1 mdA upb (ex_uolen cx) HARa HinU HFRS1 HFaddr1 HK1)
  as (KA1 & KF1 & KSH1 & KB1).
(* ---- +0x994 .. +0x998: mv a0,s4 and the jal into the free wrapper ---- *)
assert (HFRS2 : frames S2 = [(DEC_FCLASS, d_fpos cx)]) by (rewrite Hfrs2; exact HFRS1).
assert (HFaddr2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. pose proof HJ2 as (_ & Hly2 & _).
  destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (HPX : Permutation (ablocks B ly2 S2) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))])).
{ rewrite Ebl2. pose proof HPERM as HP'. rewrite Ebl1 in HP'.
  unfold ex_blocks in HP'. cbn [app] in HP'.
  replace (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx)); (upb, ex_uolen cx)])
    with ((ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))]) ++ (upb, ex_uolen cx) :: [])
    in HP' by (rewrite <- app_assoc; reflexivity).
  pose proof (Permutation_app_inv l1 l2 (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))]) []
    (upb, ex_uolen cx) HP') as Hq.
  rewrite app_nil_r in Hq. exact Hq. }
assert (HinR2 : List.In (res, dec_a_len (d_n cx)) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym HPX)). apply in_or_app; right; left; reflexivity. }
pose proof (xf_E_img regs2) as HEIb.
pose proof (xf_seat0 (fx := fx') W2 regs2 mem2 0x994) as HSb.
change (mkSS 0x994 sr_atoms [] None (mkFacts [] [] [])) with xf_ss2 in HSb.
assert (SHOKb : sh_ok SEGS (SOff 32 0) (@nil shent) (xf_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ2 as HJb.
paj_run_tok RUN HSb HJb SHOKb Bspan; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdB := mdx) in *; clearbody mdB end.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a).
{ intros a Ha.
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
    refine (kept_of_frame Ex rsx Hh m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    let wsv := eval vm_compute in (windows rsx) in change (windows rsx) with wsv end.
  intros bb wlo whi x Hin Hr. cbn [In] in Hin. destruct Hin. }
pose proof (xf_E_agree regs2) as HAEb.
assert (HPRb : aregs_preserved regs2 (ms_regs ms0))
  by (eapply aregs_preserved_of_st_ok; [exact HSb | exact HAEb | vm_compute; reflexivity]).
assert (R20b : YK11.getr regs2 20 = w64 res)
  by (transitivity (YK11.getr (ms_regs ms) 20);
      [exact (HP2 20 ltac:(unfold acallee_saved; lia))
      | transitivity (YK11.getr regs1 20); [exact (HPRa 20 ltac:(unfold acallee_saved; lia)) | exact R20]]).
reg_at HSb (10%bv : bv 5) (w64 res) Qb0
  ltac:(cbn [sv_denot]; rewrite (xf_E_reg regs2 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20b).
reg_at HSb (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x99c)) Qrb ltac:(apply codeptr_val; exact HEIb).
assert (Qspb : spZ (ms_regs ms0) = d_sp1 cx).
{ unfold spZ. rewrite <- Qsp. unfold spZ. f_equal.
  transitivity (YK11.getr regs2 2); [exact (HPRb 2 ltac:(unfold acallee_saved; lia))|].
  exact (HP2 2 ltac:(unfold acallee_saved; lia)). }
assert (Qgpb : YK11.getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ transitivity (YK11.getr regs2 3); [exact (HPRb 3 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Qgp]. }
assert (Qtpb : YK11.getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ transitivity (YK11.getr regs2 4); [exact (HPRb 4 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Qtp]. }
assert (Qs0b : YK11.getr (ms_regs ms0) 8 = w64 (d_sp0 cx)).
{ transitivity (YK11.getr regs2 8); [exact (HPRb 8 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact Qs0]. }
assert (Qrazb : raZ (ms_regs ms0) = DEC_A_LLVMF + 0x99c)
  by (unfold raZ; rewrite Qrb, unsigned_lit_small by lia; rewrite HBASEeq; reflexivity).
assert (HNEV2 : st_nev S2 < EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hn2 & _).
  unfold dec_ev_86c, DEC_CRT_EV in Hkle. unfold DEC_EV_LIB in Hnev0. lia. }
assert (HSAVED2 : dec_a_saved cx (aview segs (w_H W2) (ms_mem ms0))).
{ unfold dec_a_saved. apply Forall_forall. intros o Ho.
  pose proof (xf_saved_at_range o Ho) as Hor.
  rewrite (xf_rdword_kept (aview segs (w_H W') mem1))
    by (intros i Hi; rewrite KR2 by lia; rewrite KA1 by lia; apply KR1; lia).
  exact (proj1 (Forall_forall _ _) HSAVED o Ho). }
destruct (CHAIN W2 (ms_mem ms0) ly2 S2 mdB (k + 1) (ms_regs ms0) HJb HSAVED2 Qs0b Qspb
  ltac:(rewrite Qrazb; unfold DEC_A_LLVMF, AF_LLVMFuzzerTestOneInput, decode_text; lia))
  as (ch2 & Hch2 & Hspine2).
pose proof (proj1 HJb) as HARb.
pmkst HSb.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS___interceptor_trampoline_free)) mm rom) mdx) Q)
end.
rewrite <- HPCF.
eapply SRr_bind.
{ eapply (afree04_sub segs B LAWS decode_segs_low MT (AFREE fx') W2 (ms_regs ms0) (ms_mem ms0)
    DEC_LLVMF_STK (d_sp0 cx) (@nil (Z * Z)) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 mdB (k + 1) res (dec_a_len (d_n cx)) (d_sp1 cx - d_sp0 cx)
    (Z_to_bv 64 (BASE + 0x99c)) ch2 HJb HinR2 Qb0);
  [ lia | lia | lia | lia | exact Qgpb | exact Qtpb | exact Qrb
  | apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity]
  | exact HNEV2 | exact Hch2
  | apply HTRACE; [exact Hspine2 | rewrite Qrazb; unfold DEC_LLVMF_RA_FREE; cbn [map List.In];
      right; right; left; reflexivity]
  | intros Hbad; exfalso; exact (HnotR Hbad)
  | eapply (mok_station MT S1 S2 (mo_free MT + mo_free MT) (mo_free MT) (mo_free MT));
    [exact MTL | exact HMOK | exact MLE1 | pose proof (mo_free_nonneg MT MTL); lia | lia] ]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (m1 & m2 & Ebl3 & Ebl4) & Hfrs3 & HK2
  & MLE2 & _).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx) - ASTACK) with (d_sp1 cx - ASTACK) in HK2 by lia.
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK2 by lia.
destruct (KEEP W2 W3 (ms_mem ms0) mem3 ly2 S2 mdB res (dec_a_len (d_n cx)) HARb HinR2 HFRS2 HFaddr2 HK2)
  as (KA2 & KF2 & KSH2 & KB2).
(* the three kept bundles, composed back to the cut state *)
assert (KA : forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W3) mem3 a = aview segs (w_H W') mem1 a).
{ intros a Ha. etransitivity; [exact (KA2 a Ha)|]. etransitivity; [exact (KR2 a ltac:(lia))|].
  etransitivity; [exact (KA1 a Ha)|]. apply KR1. lia. }
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W3) mem3 a = aview segs (w_H W') mem1 a).
{ intros a Ha. etransitivity; [exact (KF2 a Ha)|]. etransitivity; [exact (KR2 a ltac:(lia))|].
  etransitivity; [exact (KF1 a Ha)|]. apply KR1. lia. }
assert (KSH : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) mem3 (d_SH cx + i) = aview segs (w_H W') mem1 (d_SH cx + i)).
{ intros i Hi. etransitivity; [exact (KSH2 i Hi)|].
  etransitivity; [exact (KR2 (d_SH cx + i) ltac:(lia))|].
  etransitivity; [exact (KSH1 i Hi)|]. apply KR1. lia. }
(* ---- the final block list and the caller's payload block ---- *)
assert (HPERM3 : Permutation (ablocks B ly3 S3) (ablocks B (d_ly cx) (d_S cx))).
{ pose proof HPX as HPx. rewrite Ebl3 in HPx. rewrite Ebl4.
  pose proof (Permutation_app_inv m1 m2 (ablocks B (d_ly cx) (d_S cx)) [] (res, dec_a_len (d_n cx)) HPx) as Hq.
  rewrite app_nil_r in Hq. exact Hq. }
assert (HPAY0 : 0 < d_n cx -> List.In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))
  by (intros Hn0; destruct Hpn as [[Hz _] | [_ Hin]]; [lia | exact Hin]).
assert (HPAY2 : 0 < d_n cx -> List.In (d_p cx, d_n cx) (ablocks B ly2 S2)).
{ intros Hn0. apply (Permutation_in _ (Permutation_sym HPX)). apply in_or_app; left. exact (HPAY0 Hn0). }
assert (HPne : 0 < d_n cx ->
  (d_p cx, d_n cx) <> (upb, ex_uolen cx) /\ (d_p cx, d_n cx) <> (res, dec_a_len (d_n cx))).
{ intros Hn0. pose proof (HPAY0 Hn0) as Hin.
  split; intros Heq; [apply HnotU | apply HnotR]; rewrite <- Heq; exact Hin. }
assert (HPAYapp : 0 < d_n cx -> in_app (d_p cx) (req_size (d_n cx)) /\ 4096 <= d_p cx).
{ intros Hn0. destruct (al_blocks _ _ LAWS _ _ _ _ _ (d_p cx) (d_n cx) HAR0 (HPAY0 Hn0))
    as (_ & Hp4 & _ & Happ & _). split; [exact Happ | exact Hp4]. }
assert (KPAY : forall i, 0 <= i < d_n cx ->
  aview segs (w_H W3) mem3 (d_p cx + i) = aview segs (w_H W') mem1 (d_p cx + i)).
{ intros i Hi. pose proof (req_size_pos (d_n cx) ltac:(lia)) as (Hq1 & Hq2).
  destruct (HPne ltac:(lia)) as (HneU & HneR).
  pose proof (HPAYapp ltac:(lia)) as (Happ & Hp4). unfold in_app in Happ.
  assert (Hout : 0 <= d_p cx + i < 2 ^ 64)
    by (unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
  etransitivity; [exact (KB2 (d_p cx) (d_n cx) i (HPAY2 ltac:(lia)) HneR ltac:(lia))|].
  etransitivity; [exact (KR2 (d_p cx + i) Hout)|].
  etransitivity; [exact (KB1 (d_p cx) (d_n cx) i (HPAY ltac:(lia)) HneU ltac:(lia))|].
  exact (KR1 (d_p cx + i) Hout). }
(* ---- +0x99c .. +0x9a4: the two shadow stores, on the plain pi engine ---- *)
assert (RS11c : YK11.getr regs3 27 = w64 (d_SH cx)).
{ transitivity (YK11.getr (ms_regs ms0) 27); [exact (HP3 27 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr regs2 27); [exact (HPRb 27 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
  transitivity (YK11.getr regs1 27); [exact (HPRa 27 ltac:(unfold acallee_saved; lia)) | exact RS11]. }
assert (HFRS3 : frames S3 = [(DEC_FCLASS, d_fpos cx)]) by (rewrite Hfrs3; exact HFRS2).
assert (HinF3 : List.In (DEC_FCLASS, d_fpos cx) (frames S3)) by (rewrite HFRS3; left; reflexivity).
assert (HFaddr3 : frame_addr ly3 DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. pose proof HJ3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 DEC_FCLASS (d_fpos cx) (proj1 HJ3) HinF3)
  as (_ & HFapp3 & HFpres3 & HShp3).
rewrite HFaddr3 in HFapp3, HFpres3, HShp3. change (fs_frame_bytes DEC_FCLASS) with 64 in HFapp3, HFpres3.
change (fs_frame_bytes DEC_FCLASS / 8) with 8 in HShp3.
assert (HShpres : forall i, 0 <= i < 8 -> apresent (w_H W3) mem3 (d_SH cx + i))
  by (intros i Hi; exact (proj1 (HShp3 i Hi))).
pose proof (xf_E_img regs3) as HEIc.
pose proof (xf_seat3 (fx := fx') W3 regs3 mem3 (d_SH cx) RS11c HSHlo HSHhi HShpres) as HSc.
assert (U27c : bv_unsigned (ew (xf_E regs3) 27) = d_SH cx)
  by (rewrite (xf_E_reg regs3 27%nat 27%bv eq_refl), RS11c; unfold w64; apply unsigned_lit_small; lia).
eapply (xf_run_pi_AJ B LAWS W3 XF_FUEL 0x9a8 (xf_E regs3) xf_ss3 xf_ss3_end xf_st3_end _
  DEC_LLVMF_STK (d_sp0 cx) (@nil (Z * Z)) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
  [(DEC_FCLASS, d_fpos cx)] ly3 S3 md3 (k + 1 + 1) _ HEIc HSc xf_run3_eq I HJ3).
{ unfold xf_ss3. cbn [ss_mem].
  eapply (awr_ok_cons_gen (xf_E regs3) xf_rsh [] DEC_LLVMF_STK (d_sp0 cx) [] (ablocks B (d_ly cx) (d_S cx))
    (ablocks B ly3 S3) ly3 [(DEC_FCLASS, d_fpos cx)] 27%nat (d_SH cx) eq_refl U27c);
    [| apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi xf_rsh] in Ha.
  right. right. right. unfold in_frames. exists DEC_FCLASS, (d_fpos cx).
  split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFaddr3.
  change (fs_frame_bytes DEC_FCLASS / 8) with 8. unfold d_SH in *. lia. }
intros ms4 mat4 HSd HJ4 HFr4.
(* the run wrote only the two shadow bytes *)
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_SH cx + 4 <= a < d_SH cx + 6) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn.
  refine (kept_of_frame (xf_E regs3) (ss_mem xf_ss3) (w_H W3) mem3 (ms_mem ms4)
    (fun x => d_SH cx + 4 <= x < d_SH cx + 6) HFr4 _ a Ha Hn).
  intros bb wlo whi x Hin Hr. cbn [xf_ss3 ss_mem windows map xf_rsh In] in Hin.
  destruct Hin as [Hq | []]. injection Hq as <- <- <-.
  cbn [base_val] in Hr. rewrite U27c in Hr. lia. }
(* the two bytes the run wrote *)
pose proof (st_ok_pi_region_nth (xf_E regs3) xf_ss3_end (restrict (w_H W3) ms4) 0 _ HSd eq_refl) as HRend.
cbn [ms_mem restrict] in HRend.
assert (HB4 : aview segs (w_H W3) (ms_mem ms4) (d_SH cx + 4) = Some DEC_SH_MID).
{ etransitivity;
  [ exact (xf_chunk_aview (xf_E regs3) (w_H W3) (ms_mem ms4) (d_SH cx) 27%nat _ _ _ _ _ 4 _ HRend U27c
      ltac:(cbn [xf_ss3_end YP09.r_chunks In]; tauto)) |].
  cbn [sv_denot]. vm_compute. reflexivity. }
assert (HB5 : aview segs (w_H W3) (ms_mem ms4) (d_SH cx + 5) = Some DEC_SH_MID).
{ etransitivity;
  [ exact (xf_chunk_aview (xf_E regs3) (w_H W3) (ms_mem ms4) (d_SH cx) 27%nat _ _ _ _ _ 5 _ HRend U27c
      ltac:(cbn [xf_ss3_end YP09.r_chunks In]; tauto)) |].
  cbn [sv_denot]. vm_compute. reflexivity. }
(* ---- the post at +0x9a8 ---- *)
pmkst HSd. rewrite xf_run3_pc.
assert (HPRc : aregs_preserved regs3 (ms_regs ms4))
  by (eapply aregs_preserved_of_st_ok; [exact HSd | exact (xf_E_agree regs3) | vm_compute; reflexivity]).
apply SRr_ret. unfold llvm_a_st_9a8.
exists fx', ly3, S3, (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md3) mat4 md3), (k + 1 + 1).
split; [rewrite (Hpcw 0x9a8); reflexivity|].
split; [exact Hfrm1|].
split.
{ split; [exact HJ4|].
  split; [exact HFRS3|].
  split.
  { transitivity (YK11.getr regs3 8); [exact (HPRc 8 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Qs0b]. }
  split.
  { transitivity (YK11.getr regs3 9); [exact (HPRc 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 9); [exact (HP3 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs2 9); [exact (HPRb 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 9); [exact (HPRa 9 ltac:(unfold acallee_saved; lia)) | exact R9]. }
  split.
  { unfold spZ. rewrite <- Qspb. unfold spZ. f_equal.
    transitivity (YK11.getr regs3 2); [exact (HPRc 2 ltac:(unfold acallee_saved; lia))|].
    exact (HP3 2 ltac:(unfold acallee_saved; lia)). }
  split; [exact HSPR|]. split; [exact HSP32|].
  split.
  { transitivity (YK11.getr regs3 3); [exact (HPRc 3 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Qgpb]. }
  split.
  { transitivity (YK11.getr regs3 4); [exact (HPRc 4 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Qtpb]. }
  split.
  { unfold dec_a_saved. apply Forall_forall. intros o Ho.
    pose proof (xf_saved_at_range o Ho) as Hor.
    rewrite (xf_rdword_kept (aview segs (w_H W') mem1))
      by (intros i Hi; rewrite KR3 by (unfold d_SH, shadow_addr, SHADOW_OFF in *; lia); apply KA; lia).
    exact (proj1 (Forall_forall _ _) HSAVED o Ho). }
  split; [exact HF4096|]. split; [exact HFmod|].
  split.
  { intros a Ha. apply (apresent_transfer segs (w_H W3) (w_H W3) mem3 (ms_mem ms4) a).
    - lia.
    - apply (frm_img segs B LAWS ly3 S3 W3 mem3 md3 DEC_FCLASS (d_fpos cx) a (proj1 HJ3) HinF3).
      rewrite HFaddr3. change (fs_frame_bytes DEC_FCLASS) with 64. lia.
    - apply KR3; [lia | unfold in_app in HFapp3; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *; lia].
    - exact (proj1 (HFpres3 a Ha)). }
  split.
  { rewrite (xf_rdword_kept (aview segs (w_H W3) mem3))
      by (intros i Hi; apply KR3;
          [lia | unfold in_app in HFapp3; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *; lia]).
    rewrite (xf_rdword_kept (aview segs (w_H W') mem1)) by (intros i Hi; apply KF; lia). exact HFLW. }
  split.
  { intros Hn0. apply (Permutation_in _ (Permutation_sym HPERM3)). exact (HPAY0 Hn0). }
  apply (xf_garr8_kept (w_H W') (w_H W3) mem1 (ms_mem ms4) (d_p cx) _); [|exact HGARR].
  intros j Hj. rewrite length_map, <- Hplen in Hj.
  assert (Hn0 : 0 < d_n cx) by lia.
  pose proof (HPAYapp Hn0) as (Happ & Hp4). unfold in_app in Happ.
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (Hq1 & Hq2).
  rewrite KR3 by (unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *; lia).
  apply KPAY. lia. }
split; [unfold dec_ev_9a8; unfold dec_ev_86c, DEC_CRT_EV in Hkle; lia|].
split; [exact HPERM3|].
split.
{ eapply mle_weaken;
  [ exact MTL
  | eapply mle_station; [exact MTL | eapply mle_station; [exact MTL | exact HMLE | exact MLE1] | exact MLE2]
  | unfold dec_spent_9a8, dec_rest_86c; lia ]. }
split.
{ unfold dec_a_fr. split.
  { transitivity (YK11.getr regs3 19); [exact (HPRc 19 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 19); [exact (HP3 19 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs2 19); [exact (HPRb 19 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 19); [exact (HPRa 19 ltac:(unfold acallee_saved; lia)) | exact RS3]. }
  split.
  { transitivity (YK11.getr regs3 21); [exact (HPRc 21 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms0) 21); [exact (HP3 21 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs2 21); [exact (HPRb 21 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia))|].
    transitivity (YK11.getr regs1 21); [exact (HPRa 21 ltac:(unfold acallee_saved; lia)) | exact RS5]. }
  transitivity (YK11.getr regs3 27); [exact (HPRc 27 ltac:(unfold acallee_saved; lia)) | exact RS11c]. }
unfold dec_a_fsh.
split.
{ intros i Hi. rewrite KR3 by lia. rewrite KSH by lia. exact (HSHL i Hi). }
split; [exact HB4|].
split; [exact HB5|].
intros i Hi. rewrite KR3 by lia. rewrite KSH by lia. exact (HSHR i Hi).
Qed.

End exfree.
