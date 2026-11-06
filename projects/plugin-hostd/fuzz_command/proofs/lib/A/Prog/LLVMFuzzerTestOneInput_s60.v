(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment RT of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command): the call of check_round_trip (jal at 0x86970) and the return to 0x86974, by cl_callS_wideF (the callee returns at an FP state of its own, apost_baseF), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it) and A/ACh6.v (a segment statement from its continuation). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YP03 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotRec SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdRep CmdObj CmdRo CmdGlob PaCall PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c send_message_c
  check_round_trip_c check_words_c verbs_receive_c sup_reply_code_c joined_c rec_calls_copy_c xstrdup_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require HarnessPropsA HarnessPropsAProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_copy_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Notation RCC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.rcc_args.

(* ---- reads through the world's view ---- *)
Lemma rt_view_byte : forall segs H mem a b, aview segs H mem a = Some b -> 0 <= b < 256.
Proof.
intros segs H mem a b E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [x|]; cbn in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
(* the digit of base 256 at weight c of a number written with it *)
Lemma rt_digit : forall v c L d h, 0 < c -> 0 <= L < c -> 0 <= d < 256 -> v = L + c * (d + 256 * h) ->
  (v / c) mod 256 = d.
Proof.
intros v c L d h Hc HL Hd ->.
rewrite <- (Z.div_unique_pos (L + c * (d + 256 * h)) c (d + 256 * h) L) by first [lia | ring].
replace (d + 256 * h) with (d + h * 256) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. exact Hd.
Qed.
(* a word read with rdword is the 8-byte field of that value *)
Lemma rt_aval8_of_rdword : forall segs H mem a v,
  rdword (aview segs H mem) a = Some v -> aval_mem (aview segs H mem) a 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v E. unfold rdword in E.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate E].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate E].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate E].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate E].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate E].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate E].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate E].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate E].
injection E as <-.
pose proof (rt_view_byte _ _ _ _ _ E0) as B0. pose proof (rt_view_byte _ _ _ _ _ E1) as B1.
pose proof (rt_view_byte _ _ _ _ _ E2) as B2. pose proof (rt_view_byte _ _ _ _ _ E3) as B3.
pose proof (rt_view_byte _ _ _ _ _ E4) as B4. pose proof (rt_view_byte _ _ _ _ _ E5) as B5.
pose proof (rt_view_byte _ _ _ _ _ E6) as B6. pose proof (rt_view_byte _ _ _ _ _ E7) as B7.
remember (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) as v eqn:Ev.
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; lia).
split; [|exact Hv].
intros k Hk. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v) by exact Hv.
rewrite Z.shiftr_div_pow2 by lia.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | | lia].
- change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, E0. f_equal. symmetry.
  change (2 ^ (8 * Z.of_nat 0)) with 1.
  apply (rt_digit v 1 0 b0 (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 1) with (a + 1). rewrite E1. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 1)) with 256.
  apply (rt_digit v 256 b0 b1 (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 2) with (a + 2). rewrite E2. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 2)) with 65536.
  apply (rt_digit v 65536 (b0 + 256 * b1) b2 (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 3) with (a + 3). rewrite E3. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  apply (rt_digit v 16777216 (b0 + 256 * b1 + 65536 * b2) b3 (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 4) with (a + 4). rewrite E4. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  apply (rt_digit v 4294967296 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) b4 (b5 + 256 * (b6 + 256 * b7)));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 5) with (a + 5). rewrite E5. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 5)) with 1099511627776.
  apply (rt_digit v 1099511627776 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4) b5 (b6 + 256 * b7));
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 6) with (a + 6). rewrite E6. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 6)) with 281474976710656.
  apply (rt_digit v 281474976710656
    (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 + 1099511627776 * b5) b6 b7);
    [lia | lia | lia | subst v; ring].
- change (a + Z.of_nat 7) with (a + 7). rewrite E7. f_equal. symmetry. change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936.
  apply (rt_digit v 72057594037927936
    (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 + 1099511627776 * b5 + 281474976710656 * b6) b7 0);
    [lia | lia | lia | subst v; ring].
Qed.

(* an element of the first part of a list without repetition is not in the second *)
Lemma rt_nodup_app : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x HN Hx Hx2; [destruct Hx|].
cbn [app] in HN. apply NoDup_cons_iff in HN as [Hn Hd]. destruct Hx as [<- | Hx].
- apply Hn, in_or_app. right. exact Hx2.
- exact (IH l2 x Hd Hx Hx2).
Qed.

(* the program's statics lie low in the image *)
Lemma rt_PG_low : forall a, inFP cmd_PG a -> 0x5e3740 <= a < 0x5e3c64.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma rt_PG_closed : ~ YI16.sink_open_fp cmd_PG.
Proof.
apply sink_closed_pos. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING.
repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.
(* the code table's index is below its length, so the code a header picks is declared *)
Lemma rt_msg_cd_declared : forall hdr, declared (SlotSpec.msg_cd hdr) = true.
Proof.
intros hdr. unfold declared, SlotSpec.msg_cd. apply existsb_exists.
exists (nth (Z.to_nat ((SlotSpec.hbyte hdr 0 / 2) mod 58)) rec_codes 0). split; [|apply Z.eqb_refl].
apply nth_In. rewrite rec_codes_length. pose proof (Z.mod_pos_bound (SlotSpec.hbyte hdr 0 / 2) 58 ltac:(lia)). lia.
Qed.
(* the message of a pass has at most 8192 bytes (SlotSpec.v msg_len) *)
Lemma rt_len_D : forall pl n r, 0 < r -> Z.of_nat (length (lt_D pl n r)) <= 8192.
Proof.
intros pl n r Hr.
assert (H2 : (length (lt_D pl n r) <= Z.to_nat (lt_len pl n r))%nat) by (unfold lt_D; rewrite length_firstn; lia).
pose proof (lt_len_range pl n r Hr) as H3.
assert (H4 : lt_len pl n r <= 8192) by (unfold lt_len, SlotSpec.msg_len; lia).
lia.
Qed.
(* its words: fewer than 2^31, their pointers fit words_of's array, joined they fit MESSAGE_MAX, and the three words
   blocks hold at most LT_WORDSB bytes (fuzz_command's plain lib/Prog/SlotRec.v words_count, line_len,
   join_need_words) *)
Lemma rt_words_bounds : forall D text copy arr, Z.of_nat (length D) <= 8192 ->
  Z.of_nat (length (Verbs.words (Verbs.line D))) < 2 ^ 31 /\
  8 * Z.of_nat (length (Verbs.words (Verbs.line D))) <= SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length D)) D) /\
  PJoinR.join_need (Verbs.words (Verbs.line D)) + 1 <= LMAX + 2 /\
  bsum (lt_wblocks D text copy arr) <= LT_WORDSB.
Proof.
intros D text copy arr HLD.
pose proof (SlotWords.sw_strnlen_upto0 D) as HL0.
pose proof (upto_len (fun b => bv_unsigned b =? 0) D) as HUD.
change (Verbs.upto (fun b => bv_unsigned b =? 0) D) with (Verbs.upto0 D) in HUD.
pose proof (SlotRec.words_count (Verbs.line D)) as HWC.
pose proof (SlotRec.line_len D) as HLL.
pose proof (SlotRec.join_need_words (Verbs.line D)) as HJW.
unfold lt_wblocks, LT_WORDSB, SlotSpec.arr_size, LMAX. cbv zeta. rewrite HL0. cbn [bsum snd].
remember (length (Verbs.words (Verbs.line D))) as nw eqn:Enw.
remember (length (Verbs.line D)) as nl eqn:Enl.
remember (length (Verbs.upto0 D)) as nu eqn:Enu.
remember (length D) as nd eqn:End.
remember (PJoinR.join_need (Verbs.words (Verbs.line D))) as jn eqn:Ejn.
clear Enw Enl Enu End Ejn HL0.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, never restated *)
Hypothesis HCHECK_ROUND_TRIP : forall fx0 : YK11.FPState, @tcheck_round_trip_spec fx0 rc SK PI B MT.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.

(* the program's statics are program statics of the record *)
Lemma rt_PG_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hr & Ha). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* every byte of check_round_trip's footprint (the recorder's blocks and the program's statics) is below the
   stack *)
Lemma rt_FP_low : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) a,
  AR SEGS B ly S W mem md -> (forall b, In b O -> In b (ablocks B ly S)) ->
  inFP (ablocks_fp O ++ cmd_PG) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO HF. pose proof asan_consts as (C1 & _).
apply inFP_app in HF as [(rr & Hr & Ha) | HP].
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & H4 & Hc & _). lia.
- pose proof (rt_PG_low a HP). lia.
Qed.

(* arodata_okP is kept along the walk's journal: the read-only bytes are image bytes outside cmd_PG *)
Lemma rt_aro_kept : forall cx ly S (W : world SEGS) mem md own k,
  arodata_okP SEGS RLO RHI B (rdW (x_W cx) (x_mem cx)) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) own ly S W mem md k ->
  arodata_okP SEGS RLO RHI B (rdW W mem).
Proof.
intros cx ly S W mem md own k HR HJ a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Hn : ~ inFP cmd_PG a) by (intros Hp; exact (cif_prog_not_ro _ _ IMG a Hp Hro)).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed cmd_PG a rt_PG_closed Hn)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img _ _ IMG a Hgot)].
Qed.

(* the arguments the recorder holds are strings of at most LMAX bytes (CmdRep.v ag1_calls) *)
Lemma rt_rcc_args_len : forall ly S rd R O, rec_repA B ly S rd R O ->
  Forall (fun x => Z.of_nat (length x) + 1 <= 32784) (RCC (r_calls R)).
Proof.
intros ly S rd R O (Q & HA & _). destruct HA as (_ & _ & _ & (_ & Hlen & _ & Hcalls & _) & _).
apply Forall_forall. intros x Hx.
unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.rcc_args in Hx.
apply in_concat in Hx as (l & Hl & Hxl). apply in_map_iff in Hl as (c & <- & Hc).
apply List.In_nth_error in Hc as (i & Hi). change (@nth_error rcall (r_calls R) i = Some c) in Hi.
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP.
2: { apply List.nth_error_None in HP.
     assert (Hlt : (i < length (r_calls R))%nat) by (apply (proj1 (List.nth_error_Some (r_calls R) i)); rewrite Hi; discriminate).
     lia. }
destruct (Hcalls i c P Hi HP) as [_ HF]. rewrite Forall_forall in HF. specialize (HF x Hxl). unfold LMAX in HF. lia.
Qed.

(* ---- the segment: from the entry of check_round_trip (0x87fd8, called at 0x86970) to 0x86974 ---- *)
Lemma lt_call_RT : forall m, LTA_F B MT m -> LT_RT_stmt B MT m.
Proof.
intros m HF. unfold LT_RT_stmt.
intros cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HRM HBODY Hr H19 H20 H26 H27 H1 H10 H11 H12 H21 Rst Rho.
cbv zeta.
set (D := lt_D (x_pl cx) (x_n cx) r).
set (R0 := lt_R0 (x_pl cx) (x_n cx) r Rh).
set (ws := lt_ws (x_pl cx) (x_n cx) r).
set (rest' := x_rest cx (lt_r' (x_pl cx) (x_n cx) r)).
destruct (vr_runA (RecModel.rec_clear R0) D) as [[R1 xr] quit] eqn:Erun.
intros HW HREC HBUD.
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HBASE as (HPRE & HROD & HRO & HVO & _ & _ & Hpn & Hlen & _ & Hfr0 & _ & Hev & Hlive & Hmo & HSTKP).
pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _).
pose proof Hstk0 as (Hal0 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & _).
pose proof HBODY as (HFRM & HSLOTS & H8 & H9 & H18 & H22 & Hm32 & Hn & Hpin).
pose proof HFRM as (HJ & Hsp & Hgp & Htp & HSAVED).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfr & Hnev & Hk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HW as (H24 & H23 & H25 & Wtext & Wcopy & Warr & Wn & Hwl & Hwp & Hww).
pose proof HREC as (HRR & Hspill & H2c & Hq & Hqr & Hperm).
pose proof HBUD as (Hk0 & Hrem0 & Hkrem & Hmle & Hacc0 & Haccx).
set (L0 := StrFun.strnlen_res (Z.of_nat (length D)) D) in *.
assert (WL : LTOI_STK = 32768) by reflexivity.
assert (WS1 : 0 <= CHECK_ROUND_TRIP_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS2 : CHECK_ROUND_TRIP_STK - -256 <= LTOI_STK) by (apply Z.leb_le; vm_compute; reflexivity).
(* ---- the message and its words ---- *)
assert (HLD : Z.of_nat (length D) <= 8192) by exact (rt_len_D (x_pl cx) (x_n cx) r (proj1 Hr)).
destruct (rt_words_bounds D text copy arr HLD) as (HNW & HARR & HJN & HWB).
change (Verbs.words (Verbs.line D)) with ws in HNW, HARR, HJN.
change (StrFun.strnlen_res (Z.of_nat (length D)) D) with L0 in HARR.
(* ---- the blocks ---- *)
set (rest := x_bl0 B cx ++ lt_wblocks D text copy arr).
pose proof (Permutation_NoDup Hperm (lt_ablocks_NoDup B LAWS ly S W mem md HAR)) as HND.
assert (HinO : forall b, In b O1 -> In b (ablocks B ly S)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hb. }
assert (HnotE : forall b, In b O1 -> ~ In b (ablocks B (x_ly cx) (x_S cx))).
{ intros b Hb He. apply (rt_nodup_app O1 (x_bl0 B cx ++ lt_wblocks D text copy arr) b HND Hb).
  apply in_or_app. left. exact He. }
assert (HinC : In (copy, L0 + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right.
  unfold lt_wblocks. cbv zeta. right. left. reflexivity. }
assert (HinA : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right.
  unfold lt_wblocks. cbv zeta. right. right. left. reflexivity. }
assert (HARR8 : arr mod 8 = 0).
{ destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR HinA) as (Ha16 & _). Z.div_mod_to_equations. lia. }
assert (HINARR : in_blockA rest arr (8 * Z.of_nat (length ws))).
{ exists arr, (SlotSpec.arr_size L0). split; [|lia].
  unfold rest. apply in_or_app. right. unfold lt_wblocks. cbv zeta. right. right. left. reflexivity. }
destruct (rt_aval8_of_rdword SEGS (w_H W) mem _ _ Warr) as [HARRV HARRR].
assert (HWK : forall kk, (kk < length ws)%nat ->
  aval_mem (rdW W mem) (arr + 8 * Z.of_nat kk) 8 (nth kk wp 0) /\ 0 <= nth kk wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B ly S) (nth kk wp 0) (Z.of_nat (length (nth kk ws [])) + 1) /\
  astr_atR (rdW W mem) (nth kk wp 0) (nth kk ws [])).
{ intros kk Hkk.
  destruct (nth_error wp kk) as [pt|] eqn:Ept; [|apply List.nth_error_None in Ept; lia].
  destruct (nth_error ws kk) as [w|] eqn:Ew; [|apply List.nth_error_None in Ew; lia].
  rewrite (List.nth_error_nth wp kk 0 Ept), (List.nth_error_nth ws kk [] Ew).
  destruct (rt_aval8_of_rdword SEGS (w_H W) mem _ _ (Hwp kk pt Ept)) as [HA HRg].
  destruct (Hww kk pt w Ept Ew) as (Hc1 & Hc2 & Hstr).
  split; [exact HA|]. split; [exact HRg|]. split; [|exact Hstr].
  exists copy, (L0 + 1). split; [exact HinC | lia]. }
(* ---- the recorder: the harness facts of the message (harness_props_holds_a) ---- *)
assert (HR0d : r_refuse R0 <> 0 -> declared (r_code R0) = true)
  by (intros _; exact (rt_msg_cd_declared (lt_hdr (x_pl cx) (x_n cx) r))).
assert (HFR : r_refuse R1 = r_refuse R0 /\ r_code R1 = r_code R0).
{ pose proof (HarnessPropsA.run_frame_at atoi_a R0 (fst (Verbs.receive atoi_a D)) (snd (Verbs.receive atoi_a D))) as Fr.
  rewrite <- HarnessPropsA.vr_run_out_at in Fr.
  pose proof Erun as Erun'. unfold vr_runA in Erun'. change reply_code_a with (HarnessPropsA.rcode_at atoi_a) in Erun'.
  rewrite Erun' in Fr. destruct Fr as (F1 & F2 & _). split; [exact F1 | exact F2]. }
assert (HR1d : r_refuse R1 <> 0 -> declared (r_code R1) = true).
{ destruct HFR as (E1 & E2). rewrite E1, E2. exact HR0d. }
pose proof (HarnessPropsAProof.harness_props_holds_a R0 D
  ltac:(apply Nat2Z.inj_le; change (Z.of_nat 8192) with 8192; exact HLD) Rst Rho HR0d) as HM.
unfold HarnessPropsA.msg_props_at in HM. cbv zeta in HM. unfold vr_runA in Erun. rewrite Erun in HM.
destruct HM as (_ & HM2 & HM3 & _ & _ & _ & _ & _ & _ & HMrt).
(* ---- the events, the live bytes and the meter ---- *)
pose proof (ev_from_nonneg (31 - m) R1 rest') as Hevf.
pose proof (EV_CHECK_ROUND_TRIP_ge0 R1 ws) as HEV0.
pose proof (LT_U_nonneg MT MTL) as HU.
pose proof (Z.mul_nonneg_nonneg _ _ HEV0 HU) as HEU.
pose proof (Z.mul_nonneg_nonneg _ _ Hevf HU) as HFU.
pose proof (xm_check_round_trip_le MT MTL R1 ws ltac:(unfold LMAX in HJN; lia) (rt_rcc_args_len _ _ _ _ _ HRR)) as HXLE.
pose proof (lt_rec_live B LAWS cx ly S W mem md R1 O1 _ _ HAR HREC) as HBB.
assert (HNEV : st_nev S + EV_CHECK_ROUND_TRIP R1 ws <= EV_MAX) by lia.
assert (HLIVE : blocks_bytes S + LIVE_CHECK_ROUND_TRIP <= LIVE_MAX).
{ unfold LIVE_LTOI, LT_RECB, LT_WORDSB in *.
  pose proof (Z.le_max_r LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)).
  pose proof (Z.le_max_r LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP). lia. }
(* the meter: one unit LT_U for each event, the products kept as opaque numbers *)
assert (HFU3 : (3 + ev_from (31 - m) R1 rest') * LT_U MT = 3 * LT_U MT + ev_from (31 - m) R1 rest' * LT_U MT) by ring.
assert (Hacc2 : acc + 3 * LT_U MT + EV_CHECK_ROUND_TRIP R1 ws * LT_U MT + ev_from (31 - m) R1 rest' * LT_U MT <=
  XM_LTOI MT (x_pl cx)).
{ replace (acc + 3 * LT_U MT + EV_CHECK_ROUND_TRIP R1 ws * LT_U MT + ev_from (31 - m) R1 rest' * LT_U MT)
    with (acc + (3 + EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 rest') * LT_U MT) by ring.
  exact Haccx. }
set (EU := EV_CHECK_ROUND_TRIP R1 ws * LT_U MT) in *.
set (FU := ev_from (31 - m) R1 rest' * LT_U MT) in *.
clearbody EU FU.
assert (HMO : mo_ok MT S (XM_CHECK_ROUND_TRIP MT R1 ws)).
{ apply (mo_ok_le MT MTL S _ EU); [|exact HXLE].
  apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc _ MTL Hmo Hmle HEU). lia. }
(* ---- the call ---- *)
set (K := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) => exists (R' : rstate) (O' : list (Z * Z)),
  rec_repA B ly' S' (rdW W' mem') R' O' /\
  r_calls R' = r_calls R1 /\ r_reply R' = r_reply R1 /\
  r_refuse R' = r_refuse R1 /\ r_code R' = r_code R1 /\ r_spill R' = r_spill R1 /\
  r_state R' = r_state R1 /\ r_host R' = r_host R1 /\
  aval_mem (rdW W' mem') A_G_QUITTING 4 (if quit then 1 else 0) /\
  Permutation (ablocks B ly' S') (O' ++ rest) /\
  (forall p n i, In (p, n) rest -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
  blocks_bytes S' <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP /\
  mo_le MT S S' (XM_CHECK_ROUND_TRIP MT R1 ws)).
pose proof (rt_aro_kept cx ly S W mem md [] k HROD HJ) as HAROD.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem md HAR HAROD) as HROK.
assert (HW08 : (x_sp1 cx + LT_W) mod 8 = 0).
{ clear - Hal0. unfold x_sp1, LT_W, LT_FRAME. Z.div_mod_to_equations. lia. }
assert (HASP : astack_pres ly (w_H W) mem (spZ regs)).
{ apply (lt_astack_pres B MT cx ly S W mem md [] k (spZ regs) HBASE HJ).
  rewrite Hsp. unfold x_sp1, x_sp0, LT_FRAME. rewrite WL. lia. }
unfold lt_post.
eapply srr_after_callF.
{ apply (cl_callS_wideF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_check_round_trip)) LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md k CHECK_ROUND_TRIP_STK (ablocks_fp O1 ++ cmd_PG)
    (EV_CHECK_ROUND_TRIP R1 ws) (-256) (getr regs 1) [] K HJ).
  - rewrite Hsp. unfold x_sp1, x_sp0, LT_FRAME. lia.
  - reflexivity.
  - lia.
  - exact WS1.
  - exact WS2.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - reflexivity.
  - rewrite H1. unfold w64. apply ret_ok_codeptr_v; [unfold LO_RTRA; lia | reflexivity].
  - rewrite H1. unfold w64. rewrite unsigned_lit_small by (unfold LO_RTRA; lia). unfold LO_RTRA. lia.
  - apply achain_low. unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1.
    exact (HCHECK_ROUND_TRIP fx ly S W regs mem md [] (x_sp1 cx + LT_W) (r_state Rh) (r_host Rh) arr
      (if quit then 1 else 0) wp ws R1 O1 rest HPRE1 HASP HRM HAROD HROK
      ltac:(rewrite Hfr, Hfr0; cbn [app count_cid]; apply Z.ltb_lt; vm_compute; reflexivity)
      ltac:(rewrite Hfr, Hfr0; cbn [app length]; lia)
      H10 H11 H12 Rst Rho
      ltac:(rewrite Hsp; unfold LT_W; lia)
      ltac:(rewrite Eshi; unfold x_sp1, x_sp0, LT_W, LT_FRAME; lia)
      HW08 Hwl HNW Wn HARRV HARRR HARR8 Hperm HINARR HWK HJN HRR H2c HR1d
      (fun _ => ex_intro _ xr (conj HM2 HM3)) Hqr Hq HMrt HNEV HLIVE HMO).
  - intros a Ha. apply inFP_app in Ha as [Ha | Ha].
    + right; right; left. destruct Ha as (rr & Hrr & Hra). unfold ablocks_fp in Hrr.
      apply in_map_iff in Hrr as ([p n] & <- & Hin). cbn [fst snd] in Hra.
      exists p, n. split; [exact (HinO _ Hin) | split; [exact (HnotE _ Hin) | lia]].
    + right; right; right; right; left. split; [exact Ha|].
      split; [exact (rt_PG_prog a Ha) | exact (cif_prog_img _ _ IMG a Ha)].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (rt_FP_low ly S W mem md O1 a HAR HinO Ha) as Hlo.
    unfold x_sp0 in Hw. rewrite WL in Hw, Hslo0. lia. }
(* ---- back at 0x86974 ---- *)
intros fx1 ly3 S3 W3 regs3 mem3 md3 _ Hfx (HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (R2 & O2 & HRR2 & Ec & _ & _ & _ & Esp & Est & Eho & Hq2 & Hperm2 & _ & _ & Hmle2).
assert (PR : forall (rr : bv 5) z, acallee_saved z -> Z_to_bv 5 z = rr -> getr regs3 rr = getr regs rr).
{ intros rr z Hz <-. exact (HP3 z Hz). }
assert (Q2 : getr regs3 2 = getr regs 2) by (apply (PR _ 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q3 : getr regs3 3 = getr regs 3) by (apply (PR _ 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q4 : getr regs3 4 = getr regs 4) by (apply (PR _ 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q8 : getr regs3 8 = getr regs 8) by (apply (PR _ 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q9 : getr regs3 9 = getr regs 9) by (apply (PR _ 9); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q18 : getr regs3 18 = getr regs 18) by (apply (PR _ 18); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q19 : getr regs3 19 = getr regs 19) by (apply (PR _ 19); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q20 : getr regs3 20 = getr regs 20) by (apply (PR _ 20); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q22 : getr regs3 22 = getr regs 22) by (apply (PR _ 22); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q23 : getr regs3 23 = getr regs 23) by (apply (PR _ 23); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q24 : getr regs3 24 = getr regs 24) by (apply (PR _ 24); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q25 : getr regs3 25 = getr regs 25) by (apply (PR _ 25); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q26 : getr regs3 26 = getr regs 26) by (apply (PR _ 26); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q27 : getr regs3 27 = getr regs 27) by (apply (PR _ 27); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
(* the frame above check_round_trip's window is kept: it is stack, outside the callee's footprint *)
assert (KEEP : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite WL in Hslo0. unfold x_sp1, x_sp0, LT_FRAME in Ha.
  apply F1.
  - lia.
  - unfold x_sp0. lia.
  - intros Hf. pose proof (rt_FP_low ly S W mem md O1 a HAR HinO Hf). lia. }
assert (HSAVED3 : lt_saved cx (rdW W3 mem3)).
{ intros i rr Hi. rewrite (rdword_ext (rdW W mem) (rdW W3 mem3)); [exact (HSAVED i rr Hi)|].
  assert (Hi13 : (i < 13)%nat)
    by (change 13%nat with (length LT_SAVED); apply (proj1 (List.nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
  intros kk Hkk. apply KEEP. unfold x_sp1, x_sp0, LT_FRAME. lia. }
assert (HSLOTS3 : lt_slots cx (rdW W3 mem3)).
{ intros o v Hin. rewrite (rdword_ext (rdW W mem) (rdW W3 mem3)); [exact (HSLOTS o v Hin)|].
  assert (Ho : 0 <= o <= 80).
  { unfold LT_SLOTS in Hin.
    repeat (destruct Hin as [E | Hin]; [apply (f_equal fst) in E; cbn [fst] in E; subst o; lia|]). destruct Hin. }
  intros kk Hkk. apply KEEP. unfold x_sp1, x_sp0, LT_FRAME. lia. }
assert (HBODY3 : lt_body B cx ly3 S3 W3 regs3 mem3 md3 (k + EV_CHECK_ROUND_TRIP R1 ws) m).
{ split; [split; [exact HJ3|]|].
  - split; [unfold spZ; rewrite Q2; exact Hsp|]. split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
    exact HSAVED3.
  - split; [exact HSLOTS3|]. split; [rewrite Q8; exact H8|]. split; [rewrite Q9; exact H9|].
    split; [rewrite Q18; exact H18|]. split; [rewrite Q22; exact H22|]. split; [exact Hm32|]. split; [exact Hn | exact Hpin]. }
assert (HREC3 : lt_rec B cx ly3 S3 W3 mem3 R2 O2 (if quit then 1 else 0) (lt_wblocks D text copy arr)).
{ split; [exact HRR2|]. split; [rewrite Esp; exact Hspill|]. split; [rewrite Ec; exact H2c|].
  split; [exact Hq2|]. split; [exact Hqr | exact Hperm2]. }
assert (HRK : rkey R2 = rkey R1) by (unfold rkey; rewrite Ec, Esp, Est, Eho; reflexivity).
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & HEV1 & _).
assert (HBUD3 : lt_bud MT cx S3 (k + EV_CHECK_ROUND_TRIP R1 ws) (acc + EU) (3 + ev_from (31 - m) R2 rest')).
{ unfold lt_bud. rewrite (ev_from_rkey _ R2 R1 _ HRK), HFU3.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mle_weaken MT (x_S cx) S3 (acc + XM_CHECK_ROUND_TRIP MT R1 ws) (acc + EU) MTL
    (mle_station MT (x_S cx) S S3 acc (XM_CHECK_ROUND_TRIP MT R1 ws) MTL Hmle Hmle2) ltac:(lia))|].
  split; lia. }
rewrite H1.
exact (HF fx1 cx ly3 S3 W3 regs3 mem3 md3 (k + EV_CHECK_ROUND_TRIP R1 ws) (acc + EU)
  r Rh R2 O2 (if quit then 1 else 0) text copy arr HBASE (fxrel_frm0 fx fx1 HRM Hfx) HBODY3 Hr
  (eq_trans Q19 H19) (eq_trans Q20 H20) (eq_trans Q26 H26) (eq_trans Q27 H27)
  (eq_trans Q24 H24) (eq_trans Q23 H23) (eq_trans Q25 H25) HREC3 HBUD3).
Qed.

End e.
End f.
End d.
