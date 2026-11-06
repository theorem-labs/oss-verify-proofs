(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the last two steps of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86958 .. the jal to check_round_trip at 0x86970), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the symbolic state at a point inside the function) and lib/A/Prog/check_refusal_s1.v (cr_entry): the symbolic state at 0x86958 and 0x86964 with the one frame word the step loads, and the transport of the cut's facts to a state that keeps the frame, the live blocks and the program's statics. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* The symbolic state at 0x86958 (pc LO_K3, the word at sp + 112) and at 0x86964 (pc LO_K4, the word at sp + 104):
   the registers are atoms 0..31 of the state's registers, atom 32 is the frame word the step loads (8 bytes, no
   inline check), held by a read-only stack region of one chunk; atom 2 (sp = sp1) is 16-aligned. No shadow entry:
   the steps make no ASan check. *)
Definition KRx : sv := SLit LT_SB.
Definition KRspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition kr_rs (off : Z) : smem :=
  [YP09.mkRegion (Some 2%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))]].
Definition kr_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition kr_ss (pc off : Z) : sstate := mkSS pc sr_atoms (kr_rs off) None kr_facts.
(* the callee-saved registers other than s5 (x21), which 0x86958 reloads *)
Definition KR_REGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.

Ltac kr_in := unfold KR_REGS; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac kr_cs := match goal with |- acallee_saved ?t => let v := eval vm_compute in t in change t with v end;
  unfold acallee_saved; lia.

(* a callee-saved register kept by a callee (aregs_preserved is stated over Z_to_bv 5 z) *)
Lemma kr_pres_loc : forall (regs regs' : bvmap 5 word) (rr : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned rr) -> getr regs' rr = getr regs rr.
Proof.
intros regs regs' rr HP Hc. pose proof (HP (bv_unsigned rr) Hc) as H.
assert (Hr : Z_to_bv 5 (bv_unsigned rr) = rr).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range 5 rr). }
rewrite Hr in H. exact H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition kr_E (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).

(* the seed: the state at BASE + pc with the frame word at sp + off *)
Lemma kr_seed_loc : forall (W : world SEGS) (regs : bvmap 5 word) mem pc off v,
  regions_wf (kr_rs off) = true ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= off <= 256 ->
  rdword (rdW W mem) (spZ regs + off) = Some v ->
  st_ok_pi SEGS VAL (kr_E regs v) (kr_ss pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS KRx [] (kr_E regs v) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc off v Hwf Hsp Hal Hoff Hv.
set (E := kr_E regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 v]) n)
  by (intros n Hn; subst E; unfold kr_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (lt_rdword_rng SEGS (w_H W) mem _ _ Hv) as Rv.
split.
- unfold kr_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold kr_E. apply regs_ok_Eimg_Ereg.
  + exact Hwf.
  + unfold kr_rs. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (spZ regs) off 8 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ Hv).
  + unfold kr_rs. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [kr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [|exact I]. split; [lia|]. split; [exact Hal | lia].
- unfold sh_ok. constructor.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the two frame words lt_kregs keeps are 64-bit values (the cut file's lt_rdword_rng) *)
Lemma lt_kregs_rng_loc : forall cx regs (W : world SEGS) mem m r Rh,
  lt_kregs cx regs (rdW W mem) m r Rh -> 0 <= r_state Rh < 2 ^ 64 /\ 0 <= r_host Rh < 2 ^ 64.
Proof.
intros cx regs W mem m r Rh (_ & _ & _ & _ & _ & Hh & Hs).
exact (conj (lt_rdword_rng SEGS (w_H W) mem _ _ Hs) (lt_rdword_rng SEGS (w_H W) mem _ _ Hh)).
Qed.

(* every point of the walk is within the event budget the entry has *)
Lemma lt_nev_loc : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  lt_bud MT cx S k acc rem -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W mem md k acc rem HBASE HJ (Hk & Hrem & Hkr & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
revert Hk Hrem Hkr Hnev Hev. generalize (EV_LTOI (x_pl cx)). intros. lia.
Qed.

(* the cut's facts at a state that keeps the frame [sp1, sp0), the live blocks and the program's statics, with the
   callee-saved registers other than s5 and the journal from the entry *)
Lemma kr_state_keep_loc : forall cx ly S (W : world SEGS) regs mem md k ly' S' (W' : world SEGS) regs' mem' md' k'
  m r Rh R O q text copy arr wp,
  lt_body B cx ly S W regs mem md k m -> lt_kregs cx regs (rdW W mem) m r Rh ->
  lt_words cx regs (rdW W mem) (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp ->
  lt_rec B cx ly S W mem R O q (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly' S' W' mem' md' k' ->
  (forall rr, In rr KR_REGS -> getr regs' rr = getr regs rr) ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, (x_sp1 cx <= a < x_sp0 cx \/ (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
     inFP cmd_PG a) -> rdW W' mem' a = rdW W mem a) ->
  lt_body B cx ly' S' W' regs' mem' md' k' m /\ lt_kregs cx regs' (rdW W' mem') m r Rh /\
  lt_words cx regs' (rdW W' mem') (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp /\
  lt_rec B cx ly' S' W' mem' R O q (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr).
Proof.
intros cx ly S W regs mem md k ly' S' W' regs' mem' md' k' m r Rh R O q text copy arr wp
  HBODY HKR HWORDS HREC HJ' HR HPERM HK.
assert (KF : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W' mem' a = rdW W mem a) by (intros a Ha; apply HK; left; exact Ha).
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> rdW W' mem' a = rdW W mem a)
  by (intros p n a Hp Ha; apply HK; right; left; exists p, n; split; [exact Hp | exact Ha]).
assert (KG : forall a, inFP cmd_PG a -> rdW W' mem' a = rdW W mem a) by (intros a Ha; apply HK; right; right; exact Ha).
assert (Hsp01 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (RW : forall a v, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> rdword (rdW W mem) a = Some v ->
  rdword (rdW W' mem') a = Some v).
{ intros a v H1 H2 H. rewrite (rdword_ext (rdW W mem) (rdW W' mem') a); [exact H|]. intros j Hj. apply KF; lia. }
destruct HBODY as (HFR & HSL & H8 & H9 & H18 & H22 & Hm & Hn & Hpn).
destruct HFR as (_ & Hsp & H3 & H4 & HSV).
destruct HKR as (Hr & H19 & H20 & H26 & H27 & HWh & HWs).
destruct HREC as (HREP & HSP & HCL & HQ & RQ & HPR).
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as (HL0 & _ & _ & H8ws & _).
assert (HINB : forall pn, In pn (O ++ x_bl0 B cx ++ lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  In pn (ablocks B ly S)) by (intros pn Hq; exact (Permutation_in _ (Permutation_sym HPR) Hq)).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hq; apply HINB; apply in_or_app; left; exact Hq).
split; [|split; [|split]].
- (* lt_body *)
  split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Hm | split; [exact Hn | exact Hpn]]]]]]]].
  + split; [exact HJ'|]. split; [unfold spZ; rewrite (HR 2%bv ltac:(kr_in)); exact Hsp|].
    split; [rewrite (HR 3%bv ltac:(kr_in)); exact H3|]. split; [rewrite (HR 4%bv ltac:(kr_in)); exact H4|].
    intros i rr Hi. specialize (HSV i rr Hi).
    assert (Hi13 : (i < 13)%nat).
    { pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hi; discriminate)) as Hlt.
      cbn [LT_SAVED length] in Hlt. exact Hlt. }
    apply RW; [lia | lia | exact HSV].
  + intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 0 <= o <= 80).
    { unfold LT_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Heq|Hin]; [injection Heq as Heq _; lia|]). destruct Hin. }
    apply RW; [lia | lia | exact HSL].
  + rewrite (HR 8%bv ltac:(kr_in)). exact H8.
  + rewrite (HR 9%bv ltac:(kr_in)). exact H9.
  + rewrite (HR 18%bv ltac:(kr_in)). exact H18.
  + rewrite (HR 22%bv ltac:(kr_in)). exact H22.
- (* lt_kregs *)
  split; [exact Hr|]. split; [rewrite (HR 19%bv ltac:(kr_in)); exact H19|].
  split; [rewrite (HR 20%bv ltac:(kr_in)); exact H20|]. split; [rewrite (HR 26%bv ltac:(kr_in)); exact H26|].
  split; [rewrite (HR 27%bv ltac:(kr_in)); exact H27|].
  split; (apply RW; [unfold LT_HOSTB, LT_STATEB; lia | unfold LT_HOSTB, LT_STATEB; lia |]); assumption.
- (* lt_words *)
  unfold lt_words in HWORDS |- *. cbv zeta in HWORDS |- *.
  destruct HWORDS as (W24 & W23 & W25 & WT & WC & WA & WN & WL & WP & WS).
  set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
  assert (HARR : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
  { apply HINB. apply in_or_app; right. apply in_or_app; right. unfold lt_wblocks. cbn [In]. right; right; left. reflexivity. }
  assert (HCPY : In (copy, L0 + 1) (ablocks B ly S)).
  { apply HINB. apply in_or_app; right. apply in_or_app; right. unfold lt_wblocks. cbn [In]. right; left. reflexivity. }
  pose proof (req_size_pos (SlotSpec.arr_size L0) ltac:(unfold SlotSpec.arr_size; pose proof (Z.div_pos L0 2); lia))
    as [_ HRA].
  pose proof (req_size_pos (L0 + 1) ltac:(lia)) as [_ HRC].
  split; [rewrite (HR 24%bv ltac:(kr_in)); exact W24|]. split; [rewrite (HR 23%bv ltac:(kr_in)); exact W23|].
  split; [rewrite (HR 25%bv ltac:(kr_in)); exact W25|].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WT]|].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WC]|].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WA]|].
  split; [apply (aval_mem_kept_r (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in *;
    cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact WN]|].
  split; [exact WL|]. split.
  + intros i pt Hi. specialize (WP i pt Hi).
    assert (Hil : (i < length (lt_ws (x_pl cx) (x_n cx) r))%nat)
      by (rewrite <- WL; apply nth_error_Some; rewrite Hi; discriminate).
    rewrite (rdword_ext (rdW W mem) (rdW W' mem') (arr + 8 * Z.of_nat i)); [exact WP|].
    intros j Hj. apply (KB arr (SlotSpec.arr_size L0)); [exact HARR | lia].
  + intros i pt w Hi Hw. destruct (WS i pt w Hi Hw) as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact C2|].
    apply (astr_atR_kept_r (rdW W mem)); [|exact C3].
    intros x Hx. apply (KB copy (L0 + 1)); [exact HCPY | lia].
- (* lt_rec *)
  split; [|split; [exact HSP|split; [exact HCL|split; [|split; [exact RQ | exact (perm_trans HPERM HPR)]]]]].
  + apply (rec_repA_kept B ly S (rdW W mem) ly' S' (rdW W' mem') R O HREP).
    * intros pn Hq. exact (Permutation_in _ (Permutation_sym HPERM) (HO pn Hq)).
    * intros a [Ha | [Ha | Ha]].
      -- apply KG. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | unfold REC_SIZE in Ha; cbn [fst snd]; lia].
      -- apply KG. exists (A_REC_SPILL, A_REC_SPILL + 56).
         split; [right; left; reflexivity | unfold SC_SIZE in Ha; cbn [fst snd]; lia].
      -- destruct Ha as (rg & Hrg & Hrga). unfold ablocks_fp in Hrg. apply in_map_iff in Hrg as ([p n] & <- & Hq).
         cbn [fst snd] in Hrga. exact (KB p n a (HO _ Hq) Hrga).
  + apply (aval_mem_kept_r (rdW W mem)); [|exact HQ].
    intros x Hx. apply KG. exists (A_G_QUITTING, A_G_QUITTING + 4).
    split; [right; right; left; reflexivity | cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia].
Qed.
End e.
End f.
End d.
