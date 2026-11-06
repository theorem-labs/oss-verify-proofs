(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_td: the teardown of image B's LLVMFuzzerTestOneInput, from the join +0xae0
   (llvm_b_st_ae0 of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) to the slot post at the return (dec_b_post).
   The code (lib/B/Prog/DecodeBList.v, offsets from the entry):
     +0xae0..+0xae8  lui/addiw a0 = 0x45e0360e, sd a0, 0(a7)      the fake frame's record word: freed magic
     +0xaec          beqz a6, +0xb20                               not taken: a6 = the fake frame, >= 4096
     +0xaf0..+0xb10  li a0,-11; sb a0, 0..7(t0)                    the frame's 8 shadow bytes := 0xf5
     +0xb14 / +0xb18 ld a0, 56(a6); sb zero, 0(a0)                 the flag byte := 0: the stack free
     +0xb1c          j +0xb40
     +0xb40..+0xb7c  li a0,0; addi sp,s0,-224; 13 reloads; addi sp,sp,224
     +0xb80          ret
   The form is cgif's teardown stage rt_XP (proofs/cgif/cgif_file_fuzzer/lib/A/ACf4.v:78-117 at origin/ossv/recipes):
   one symbolic run that includes the flag store (YCbq.v aj_flag_store, the stack_free_state of the fake frame),
   then SRr_ret_at, then the slot post out of the journal. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa
  DecodeBPaLib DecodeBImg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180 lf_lia_orig / lf_nia_orig). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.

(* The teardown's absolute pc (DEC_A_LLVMF + 0xae0) and the return's (+ 0xb80). *)
Definition TD_PC : Z := 527248.
Lemma td_pc_eq : DEC_A_LLVMF + 0xae0 = TD_PC.
Proof. vm_compute. reflexivity. Qed.

(* The run's symbolic state at +0xae0. Atoms 0..31 are the registers at the join; atom 32 is the flag address
   d_FL; atoms 33..45 are the caller's 13 callee-saved words, in dec_b_saved_at's order. Regions: the fake frame's
   record word (written, base a7 = atom 17), its flag-pointer word at +56 (read, base a6 = atom 16), its 8 shadow
   bytes (written, base t0 = atom 5), the flag byte (written, base atom 32), and the 13 saved words below the entry
   sp (read, base s0 = atom 8). *)
Definition td_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45 0)) ].
Definition td_rs : smem :=
  [ YP09.mkRegion (Some 17%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 16%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 5%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 td_chunks ].
Definition td_facts : facts := mkFacts [(16%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition td_ss : sstate := mkSS TD_PC sr_atoms td_rs None td_facts.

Section td. Context {rc : YM05.RunCeil}.
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
Local Abbreviation segs := decodesegsB0.

Definition td_extra (cx : dctx) : list word :=
  w64 (d_FL cx) :: map (fun o : Z * Z => YK11.getr (d_regs cx) (Z_to_bv 5 (snd o))) dec_b_saved_at.

Section f. Context {fx : YK11.FPState}.

Ltac td_base_val Ex n v Hn :=
  replace (base_val Ex (Some n)) with v by (cbn [base_val]; rewrite Hn; symmetry; apply unsigned_lit_small; lia).

Lemma td_entry : forall (cx : dctx) (W1 : world segs) ly1 S1 regs1 mem1 md1 k1,
  dec_b_core B cx ly1 S1 W1 regs1 mem1 md1 k1 ->
  dec_b_fr cx regs1 ->
  (forall a, (d_F cx <= a < d_F cx + 64 \/ d_SH cx <= a < d_SH cx + 8) -> a <> d_FL cx) ->
  apresent (w_H W1) mem1 (d_FL cx) -> 4096 <= d_FL cx < alloc_ceiling ->
  in_app (d_F cx) 64 -> d_F cx + 64 <= alloc_ceiling ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> apresent (w_H W1) mem1 a) ->
  st_ok segs (Ereg regs1 (td_extra cx)) td_ss
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 TD_PC) mem1 (seg_rom segs))).
Proof.
intros cx W1 ly1 S1 regs1 mem1 md1 k1 Hcore Hfr HnoFL HFLp HFLr HFapp HFceil HSHp.
destruct Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
destruct Hfr as (Ht0 & Ha6 & Ha7).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
set (F := d_F cx) in *. set (FL := d_FL cx) in *. set (sp0 := d_sp0 cx) in *.
set (SH := d_SH cx) in *.
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Ereg regs1 (td_extra cx)).
assert (E5 : ew E 5 = w64 SH) by (exact (eq_trans (ew_Ereg_nat regs1 _ 5 5%bv eq_refl) Ht0)).
assert (E8 : ew E 8 = w64 sp0) by (exact (eq_trans (ew_Ereg_nat regs1 _ 8 8%bv eq_refl) Hs0)).
assert (E16 : ew E 16 = w64 F) by (exact (eq_trans (ew_Ereg_nat regs1 _ 16 16%bv eq_refl) Ha6)).
assert (E17 : ew E 17 = w64 F) by (exact (eq_trans (ew_Ereg_nat regs1 _ 17 17%bv eq_refl) Ha7)).
assert (E32 : ew E 32 = w64 FL) by (exact (ew_Ereg_extra regs1 _ 0)).
assert (HSHr : SHADOW_OFF <= SH /\ SH + 8 <= kHighShadowEnd).
{ rewrite ESH. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  assert (F / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). rewrite C2. unfold SHADOW_OFF. cbn in *. lia. }
assert (HSHF : F + 64 <= SH \/ SH + 8 <= F).
{ rewrite ESH. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
assert (HFLF : FL + 1 <= F \/ F + 64 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [H|H]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 64)) as [H'|H']; [exfalso; exact (HnoFL FL ltac:(lia) eq_refl) | right; lia]. }
assert (HFLS : FL + 1 <= SH \/ SH + 8 <= FL).
{ destruct (Z_lt_ge_dec FL SH) as [H|H]; [left; lia|].
  destruct (Z_lt_ge_dec FL (SH + 8)) as [H'|H']; [exfalso; exact (HnoFL FL ltac:(lia) eq_refl) | right; lia]. }
assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
unfold td_ss. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold td_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; fold E.
  + td_base_val E 17%nat F E17. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HFpres. lia.
  + td_base_val E 16%nat F E16. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 56 8 (SOff 32 0) FL);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (val_mem_of_rdword segs (w_H W1) mem1 _ _ HFLw).
  + td_base_val E 5%nat SH E5. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HSHp. lia.
  + td_base_val E 32%nat FL E32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HFLp.
  + td_base_val E 8%nat sp0 E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold dec_b_saved, dec_b_saved_at in Hsaved. cbn [fst snd] in Hsaved.
    repeat match type of Hsaved with Forall _ (_ :: _) =>
      apply Forall_cons_iff in Hsaved; let H := fresh "Hw" in destruct Hsaved as [H Hsaved]; cbn [fst snd] in H end.
    unfold td_chunks. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let o := eval vm_compute in (- off) in
      lazymatch goal with Hw : rdword _ (_ - o) = Some ?v |- _ =>
        apply (chunk_ok_val segs E _ sp0 off 8 (SOff n 0) v);
        [ cbn [sv_denot]; unfold E;
          let Hx := fresh "Hx" in
          pose proof (ew_Ereg_extra regs1 (td_extra cx) (n - 32)) as Hx;
          cbn [Nat.add Nat.sub nth map td_extra dec_b_saved_at snd] in Hx; rewrite Hx, Z.add_0_r; reflexivity
        | cbn; apply bv_unsigned_in_range
        | lia
        | replace (sp0 + off) with (sp0 - o) by lia; exact (val_mem_of_rdword segs (w_H W1) mem1 _ _ Hw) ]
      end end.
- apply pairwise_disjoint_of_extents. unfold td_rs, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
  td_base_val E 17%nat F E17. td_base_val E 16%nat F E16. td_base_val E 5%nat SH E5.
  td_base_val E 32%nat FL E32. td_base_val E 8%nat sp0 E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; exact I].
  cbn [td_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E16, unsigned_lit_small by lia. change (2 ^ 5) with 32. lia.
Qed.

(* The caller-journal's FP is the call's file-position budget; with no file written it may be widened (cgif
   lib/A/ACfh.v:29-44 ajournal_fp_nil, copied, at image B's segments and sink head). *)
Lemma td_journal_fp : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  @ajournal rc dec_B_sink_head segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.

(* A register after the run: its symbolic value, computed. *)
Ltac td_rg HS r :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?H ?msx) =>
    rewrite (st_ok_restrict_reg segs H Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end.
Ltac td_ew :=
  cbn [sv_denot]; rewrite ?Z.add_0_r;
  cbn [ew Ereg Nat.ltb Nat.leb Nat.sub nth td_extra map dec_b_saved_at snd fst].
(* YCbq.v's aj_run_flag, with aj_flag_store's argument count of this kit (it takes one argument more than the
   cgif text the Ltac was written for). *)
Ltac td_run_flag tblok HS HJ :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
        let HML := lazymatch goal with H : model_laws _ |- _ => H end in
        let HASF := lazymatch goal with H : astack_free_law _ _ |- _ => H end in
        let HFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end in
        eapply (aj_flag_store segs _ HL HSL HML tbl tblok HWX HASF HFFL W FUEL E ss ss' st ms
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
        [ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
      end
    end
  end.

Lemma td_main :
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (mrestrict (w_H W0) mem0) md0 -> asink_none segs tfib_K (mrestrict (w_H W') mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') M) ->
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  forall (cx : dctx) (W1 : world segs) ly1 S1 regs1 mem1 md1 k1,
  @dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_b_core B cx ly1 S1 W1 regs1 mem1 md1 k1 -> k1 <= dec_ev_ae0 ->
  Permutation (ablocks B ly1 S1) (ablocks B (d_ly cx) (d_S cx)) ->
  mo_le MT (d_S cx) S1 (dec_spent_ae0 MT (d_n cx)) ->
  dec_b_fr cx regs1 -> frm_zero (@fp_csr fx) ->
  SRr segs W1 (mkCfg (YK11.mkst regs1 (w64 (DEC_A_LLVMF + 0xae0)) mem1 (YK11.seg_rom segs)) md1)
    (@dec_b_post rc asink_syms tfib_K asink_none ameta_inv RA_LLVMF B MT XL cx).
Proof.
intros LAWS ML MTL MTF ASF FFL HSK HMK HXL cx W1 ly1 S1 regs1 mem1 md1 k1 HB Hcore Hk Hperm Hmle Hfr Hfz.
pose proof decodeb_segs_low as Hsegs. pose proof decodeb_wx as Hwx.
pose proof Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL ly1 S1 W1 mem1 md1 DEC_FCLASS (d_fpos cx) HAR Hin0) as (HFLp & HFLo & [HFLapp HFLimg] & HFL4096 & HFLz & HFLc).
destruct (frames_bounds segs B LAWS ly1 S1 W1 mem1 md1 DEC_FCLASS (d_fpos cx) HAR Hin0) as (HF1 & HF2 & HF3).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (EFA : frame_addr ly1 DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (EFL : flag_addr ly1 DEC_FCLASS (d_fpos cx) = d_FL cx) by (unfold d_FL, flag_addr; rewrite HlyF; reflexivity).
rewrite EFL in HFLp, HFLo, HFL4096, HFLc. rewrite EFA in HF1, HF2, HF3.
assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
rewrite FB in HF2, HF3.
(* the fake frame and its shadow are this function's own bytes, the flag byte is the allocator's *)
assert (Hown : forall a, (d_F cx <= a < d_F cx + 64 \/ d_SH cx <= a < d_SH cx + 8) ->
  awr_byte DEC_LLVMF_STK (d_sp0 cx) [] (ablocks B (d_ly cx) (d_S cx)) (ablocks B ly1 S1) ly1
    [(DEC_FCLASS, d_fpos cx)] a).
{ intros a Ha. right; right; right. exists DEC_FCLASS, (d_fpos cx). split; [left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite EFA, FB. change (64 / 8) with 8. unfold d_SH in Ha. lia. }
assert (HnoFL : forall a, (d_F cx <= a < d_F cx + 64 \/ d_SH cx <= a < d_SH cx + 8) -> a <> d_FL cx).
{ intros a Ha Heq. subst a.
  destruct (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (Hown _ Ha)) as (Hno & _).
  exact (Hno HFLo). }
assert (HSHp : forall a, d_SH cx <= a < d_SH cx + 8 -> apresent (w_H W1) mem1 a).
{ intros a Ha. exact (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (Hown a ltac:(lia)))). }
pose proof (td_entry cx W1 ly1 S1 regs1 mem1 md1 k1 Hcore Hfr HnoFL HFLp ltac:(lia) HF3 HF2 HSHp) as HS.
change (w64 (DEC_A_LLVMF + 0xae0)) with (Z_to_bv 64 (DEC_A_LLVMF + 0xae0)). rewrite td_pc_eq.
assert (E5 : ew (Ereg regs1 (td_extra cx)) 5 = w64 (d_SH cx))
  by (pose proof Hfr as (Ht0 & _ & _); exact (eq_trans (ew_Ereg_nat regs1 _ 5 5%bv eq_refl) Ht0)).
assert (E17 : ew (Ereg regs1 (td_extra cx)) 17 = w64 (d_F cx))
  by (pose proof Hfr as (_ & _ & Ha7); exact (eq_trans (ew_Ereg_nat regs1 _ 17 17%bv eq_refl) Ha7)).
assert (E32 : ew (Ereg regs1 (td_extra cx)) 32 = w64 (d_FL cx)) by (exact (ew_Ereg_extra regs1 _ 0)).
assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HSHr : 0 <= d_SH cx < 2 ^ 64).
{ unfold d_SH, shadow_addr. pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
  assert (d_F cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). cbn in *. lia. }
td_run_flag decodebtbl_ok HS HJ.
- unfold DEC_FCLASS. lia.
- intros a (r & Hin & Hr). rewrite EFL.
  cbn [td_ss ss_mem td_rs In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + left. apply Hown. rewrite E17, unsigned_lit_small in Hr by lia. lia.
  + lia.
  + left. apply Hown. rewrite E5, unsigned_lit_small in Hr by lia. lia.
  + right. rewrite E32, unsigned_lit_small in Hr by lia. lia.
  + lia.
- intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok _ ?Ex ?ssx _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 3) in
    lazymatch rr with Some ?r =>
      pose proof (st_ok_region_nth (segs := segs) Ex ssx msr 3 r HSr ltac:(vm_compute; reflexivity)) as HR
    end end.
  pose proof (field_of_region (segs := segs) _ _ 32 (d_FL cx) _ _ _ _ _ 0 1%N (SLit 0) 0 HR
    ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
  exact V0.
- (* the return *)
  eapply (SRr_ret_at segs decodebtbl decodebtbl_ok decodeb_wx W1 _ _ ms _ _ HS eq_refl
    ltac:(vm_compute; reflexivity)).
  intros mat2.
  pose proof (ajournal_materialize segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ) as HJ3.
  destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
    as (Hret0 & Hra0 & Hgp0 & Htp0 & _ & _ & Hpn & Hnlen & _ & _ & _ & Hsink0 & Hfss0 & Hmeta0 & _).
  pose proof HJ3 as (_ & _ & _ & _ & Hio3 & _ & _ & _ & _ & HG2 & _).
  destruct (aos_step_closed [] _ _ sink_closed_nil Hio3) as (Efd & Efsys & _ & _).
  assert (R1 : getr (ms_regs ms) 1 = getr (d_regs cx) 1).
  { td_rg HS (1%bv : bv 5). td_ew. apply Z_to_bv_bv_unsigned. }
  unfold dec_b_post.
  lazymatch goal with |- context [mkCfg _ ?mdx] =>
    exists fx, ly1, (stack_free_state DEC_FCLASS (d_fpos cx) S1), (ms_regs ms), (ms_mem ms), mdx, k1 end.
  split.
  { rewrite R1, Hret0. unfold raZ in Hra0. unfold w64. rewrite <- Hra0, Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hfz|].
  unfold dec_lib_post_x.
  split; [exact (td_journal_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|].
  split; [unfold dec_ev_ae0, DEC_EV_LIB in *; lia|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [->|Hr']); try (subst r);
    lazymatch goal with |- getr _ (Z_to_bv 5 ?rr) = _ => td_rg HS (Z_to_bv 5 rr) end;
    cbn [sv_denot]; rewrite ?Z.add_0_r;
    first
    [ rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl), Hs0; unfold w64, d_sp0, spZ;
      rewrite !Z_to_bv_bv_unsigned; first [reflexivity | f_equal; apply bv_eq; reflexivity]
    | rewrite (ew_Ereg_nat regs1 _ 3 3%bv eq_refl), Hgp, Z_to_bv_bv_unsigned;
      transitivity (getr (d_regs cx) 3); [exact (eq_sym Hgp0) | first [reflexivity | f_equal; apply bv_eq; reflexivity]]
    | rewrite (ew_Ereg_nat regs1 _ 4 4%bv eq_refl), Htp, Z_to_bv_bv_unsigned;
      transitivity (getr (d_regs cx) 4); [exact (eq_sym Htp0) | first [reflexivity | f_equal; apply bv_eq; reflexivity]]
    | td_ew; rewrite ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; apply bv_eq; reflexivity] ]. }
  split.
  { td_rg HS (10%bv : bv 5). reflexivity. }
  split.
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly1 S1). exact Hperm. }
  split.
  { intros fd. unfold m_fds. rewrite Efd. reflexivity. }
  split.
  { cbn [YO09.ll_fs]. unfold m_fs. rewrite Efsys. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hfss0|].
  split; [exact (HSK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3
    ltac:(unfold YI16.sink_open_fp, YI16.in_fp; intros (? & [] & _)) Hsink0)|].
  split; [exact (HMK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta0)|].
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTF).
    apply (mo_le_mono MT MTL _ _ _ _ Hmle).
    pose proof (dec_cost_ladder MT (d_n cx)) as (_ & _ & _ & _ & _ & _ & _ & Lae0).
    unfold dec_rest_ae0 in Lae0. pose proof (HXL (d_n cx) ltac:(rewrite Hnlen; lia)). lia. }
  { intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hinp]]; [lia|].
    apply (HG2 (d_p cx) (d_n cx) i Hinp).
    - unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly1 S1).
      exact (Permutation_in _ (Permutation_sym Hperm) Hinp).
    - pose proof (req_size_pos (d_n cx) ltac:(lia)). lia.
    - apply inFP_nil. }
Qed.
End f.

(* The teardown from the join's state, whatever float state reached it. *)
Lemma llvm_b_exit_td :
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (mrestrict (w_H W0) mem0) md0 -> asink_none segs tfib_K (mrestrict (w_H W') mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') M) ->
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
  @dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  llvm_b_st_ae0 B MT cx W' c' ->
  SRr segs W' c' (@dec_b_post rc asink_syms tfib_K asink_none ameta_inv RA_LLVMF B MT XL cx).
Proof.
intros LAWS ML MTL MTF ASF FFL HSK HMK HXL cx W' c' HB Hae.
destruct Hae as (fx' & ly1 & S1 & regs1 & mem1 & md1 & k1 & -> & Hfz & Hcore & Hk & Hperm & Hmle & Hfr & _).
exact (@td_main fx' LAWS ML MTL MTF ASF FFL HSK HMK HXL cx W' ly1 S1 regs1 mem1 md1 k1 HB Hcore Hk Hperm Hmle Hfr Hfz).
Qed.
End td.
