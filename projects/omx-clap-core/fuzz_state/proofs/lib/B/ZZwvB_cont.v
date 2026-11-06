(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v, with its module paths and module names changed; 614 of its 685 lines of code are new or changed and 351 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the CALL GLUE of the lib/B (fs.asan-ubsan) container arms of write_value:
   the four call steps of the item loop (put of a literal, indent, put_string of an object key, the recursive
   write_value of an item), each from the facts the engine run of ZZwvB_runs1 / ZZwvB_runs2 left at the call to the
   loop invariant (ZZwvB_inv.wvc_inv) at the callee's return address, through ZZwvB_call3.wvc_callpre (the callee's
   fpreU and the one-node frame chain at s0 = o) and ZZwvB_step.wvc_ret_inv (the return).
   Image A has no twin of this file: its container arms are unproved (wv_arr / wv_obj are hypotheses of
   lib/A/FSW_write_value.v); the pieces it does have are mirrored in ZZwvB_*.v with A's names.
   rule 24: proves no function (kind: segment lemma) - call steps of the container arms of write_value B.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/ZZwvB_arm.v, with its module names changed; 286 of its 336 lines of code are new or changed and 635 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the lib/B (fs.asan-ubsan) CONTAINER ARMS of write_value - the two lemmas
   wv_arr / wv_obj that lib/B/FSW_write_value.v (a Theorem Labs lane) takes as hypotheses, proved here against fs's S0 spec
   write_value_spec_at (lib/B/FSH_Fn_writer.v, statement set a working branch 50968be8342). Image A's
   arms are NOT proved anywhere (A's write_value_holds is Qed over them as hypotheses); the A pieces this file
   mirrors are a working branch 1a5dc5b2e7c lib/A/ZZwv_*.v, whose lemma names the lib/B twins
   ZZwvB_*.v keep.
   rule 24: proves no function (kind: segment lemma) - the two container arms of write_value B, not the whole
   function (the closing theorem is a Theorem Labs lane's).
   THE ARMS (fs.asan-ubsan, write_value 0x84010, frame 192; every address MEASURED on the pinned image, sha256
   5ac5ce09...): the array / object entry at 0x840b4 puts '[' / '{' (jal put 0x840d8, returning to 0x840dc), reads
   n = v->n (ASan check of v + 40 at 0x84108), and
   - n = 0: jumps to 0x842c4 and TAIL-jumps to put with ']' / '}' (j at 0x84440);
   - n <> 0: writes the loop's frame slots and runs the item loop: put of ',' (0x84188, from the second item on),
     indent (0x8419c), for an object put_string of the key (0x84214) and put of ':' / ': ' (0x84224), the recursive
     write_value of the item (0x8427c), and after the last item the closing indent (0x842c0) and the TAIL put of the
     closing bracket.
   THE NINE UBSan GUARDS on these arms (trap mode, `unimp` at 0x84444; a Theorem Labs lane's report-sites-B.tsv row 117) and
   the premise that rules each one out - each is discharged where its run meets it, by the condition / atom fact
   named at the segment lemma in ZZwvB_runs1.v / ZZwvB_runs2.v (ZZwvB_defs.v's wvc_c.. conditions and wvc_gf.. facts):
     0x8418c `bnez s10`        signed overflow of d + 1 : d + Z.of_nat (depth t) <= 2 ^ 31 - 1 and depth >= 1 for a
                               container (wvc_d1), as wvc_cSLT on the open run and s10 = 0 in wvc_ssL after it;
     0x841d8 `beq a2,a3`       "exactly one of keys, keys + 8 i is null" : both are >= 4096 (wvc_gfK: the keys block
                               is a live reader block of the tree, FSH_Fn_reader.pobj / fs_rblock);
     0x841e0 `bnez a2`         high nibble of i : i < n <= 2 ^ 54 (the node's n, pj_hdr / pj_node), wvc_cI60;
     0x841e4 `bltu a0,a1`      keys + 8 i overflows : keys + 8 n <= alloc_ceiling, wvc_cKEYS;
     0x841e8 `beqz a1`         keys is null : keys >= 4096 (wvc_gfK);
     0x841f4 `bnez a1`         keys + 8 i misaligned : the keys block is 16-aligned and i is a slot index (wvc_gfK's
                               alignment 3 on xatom 18);
     0x8424c `beq a3,a4`       the same null pair for kids : kids >= 4096 (wvc_gfA) and the range of 56 i + kids;
     0x84250 `bltu a2,a1`      kids + 56 i overflows : kids + 56 n <= alloc_ceiling, wvc_cKIDS;
     0x84268 `bnez a0`         signed overflow of 56 i : i < 2 ^ 54, wvc_cMULH.
   The TEN ASan report sites of the same rows (116, 118-126) are the inline shadow checks of v->type (0x842ac,
   0x84458, 0x8446c), v->n (0x8447c, 0x8448c), v->kids (0x84474), v->keys (0x84484), the key slot (0x84488) and the
   string / number arms' v->str (0x84494, 0x84498): the token engine discharges each from the shadow entries
   wvc_SH0 / wvc_SHK (the node's 56 bytes and the key slot's 8), i.e. from pobj and the keys block's liveness.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_rd FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs ZZwvB_arm ZZwvB_comp ZZwvB_kit ZZwvB_tree ZZwvB_inv ZZwvB_call ZZwvB_call2 ZZwvB_call3
ZZwvB_ret ZZwvB_res ZZwvB_runs1 ZZwvB_runs2 ZZwvB_step ZZwvB_arm ZZwvB_arm2 ZZwvB_entry ZZwvB_close
ZZwvB_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= the arms' helpers ================= *)
(* eight visible bytes make a word *)
Lemma wvc_rdword_some : forall (rd : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd (a + i) <> None) -> exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|] eqn:E0; [|congruence]. destruct (rd (a + 1)) as [b1|] eqn:E1; [|congruence].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|congruence]. destruct (rd (a + 3)) as [b3|] eqn:E3; [|congruence].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|congruence]. destruct (rd (a + 5)) as [b5|] eqn:E5; [|congruence].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|congruence]. destruct (rd (a + 7)) as [b7|] eqn:E7; [|congruence].
eexists. reflexivity.
Qed.

(* the word at o - 8 that every callee keeps (ZZwvB_inv.wf_ra8), with the one-node chain clause restated on it: in
   the second case of wv_chain_o the word is given; in the first, o - 8 = sp, whose 8 bytes are in the window
   [sp, ot) the presence premise covers, and a stack byte (>= kHighMemBeg) is no user-poisoned shadow byte, so the
   unpoisoned view shows them *)
Lemma wvc_ra8_entry : forall STK ly S U (W : world tfibsegs) regs mem md ch o ot,
  fpreU tfibsegs B STK ly S U W regs mem md ch -> o + 32 <= ot ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  wv_chain_o U W mem regs o ->
  exists ra8, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra8 /\
    ((o = spZ regs + 8 /\ raZ regs < alloc_ceiling) \/
     (spZ regs + 16 <= o /\ exists nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\
        (ra8 < 4096 \/ nfp < alloc_ceiling))).
Proof.
intros STK ly S U W regs mem md ch o ot (HPREU & _) Hoot HPRES HCHO.
destruct HCHO as [(Ho & Hra) | (H16 & ra & nfp & H8 & H16' & Hend)].
- pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREU) as HARU.
  pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (_ & Hceil & H47 & HS0).
  pose proof asan_consts as (C1 & _ & C3 & _).
  assert (HV : forall i, 0 <= i < 8 -> aview tfibsegs (w_H W) (unpoison U mem) (o - 8 + i) <> None).
  { intros i Hi.
    rewrite (fsw_aview_unpoison_high B ly S U W mem md (o - 8 + i) HARU) by lia.
    destruct (HPRES (o - 8 + i) ltac:(lia)) as [Hh [b Hb]].
    unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. }
  destruct (wvc_rdword_some _ (o - 8) HV) as (ra8 & H8).
  exists ra8. split; [exact H8|]. left. split; [exact Ho | exact Hra].
- exists ra. split; [exact H8|]. right. split; [exact H16|]. exists nfp. split; [exact H16' | exact Hend].
Qed.

(* the pieces of a non-empty container start with the bracket and the first indent (wvc_step_open's premise) *)
Lemma wvc_arr_rest : forall p d items, items <> [] ->
  exists Rest, WriterValue.wvpieces (PjTree.JArr items) p d = [91] :: WriterValue.wind p (d + 1) ++ Rest.
Proof.
intros p d [|u r] Hne; [congruence|].
exists (WriterValue.wvpieces u p (d + 1) ++ wv_items p d 1%nat r ++ WriterValue.wind p d ++ [[93]]).
rewrite wv_pieces_arr, wv_items_cons. cbn [WriterValue.wcomma Nat.eqb]. rewrite app_nil_l.
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_obj_rest : forall p d members, members <> [] ->
  exists Rest, WriterValue.wvpieces (PjTree.JObj members) p d = [123] :: WriterValue.wind p (d + 1) ++ Rest.
Proof.
intros p d [|[nm u] r] Hne; [congruence|].
exists (WriterSpec.spieces nm ++ [WriterValue.wsep p] ++ WriterValue.wvpieces u p (d + 1) ++ wv_mems p d 1%nat r
  ++ WriterValue.wind p d ++ [[125]]).
rewrite wv_pieces_obj, wv_mems_cons. cbn [WriterValue.wcomma Nat.eqb]. rewrite app_nil_l.
rewrite <- !app_assoc. reflexivity.
Qed.

(* ================= the two container arms ================= *)
(* The arm builds its instance F from write_value_spec_at's premises (the node's header out of PjStruct.pj_node,
   the saved word at o - 8 out of the window's presence and the one-node chain clause wv_chain_o), discharges the
   Section's entry hypotheses, and runs: the entry step (ZZwvB_entry.wvc_step_entry) to the put of the opening
   bracket, then either the empty close (ZZwvB_close.wvc_arm_empty) or the first indent (wvc_step_open) and the
   item loop (wvc_loop_arr / wvc_loop_obj), which ends in the closing tail put (ZZwvB_close.wvc_arm_close).
   At k >= 2 the arm is vacuous: PjTree.depth of a container is at least 1 and the spec asks depth <= 2 - k = 0.
   The Section hypotheses HE_.. of ZZwvB_entry / ZZwvB_close / ZZwvB_loop are proved below as local facts of the
   same names, stated on the premises' own variables (each is convertible to its F form), and each imported step is
   applied by the names of its binders, so its premises close by `assumption` whichever HE_.. its proof uses. *)
Lemma wv_arr : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on B (fun t => exists items, t = PjTree.JArr items) k.
Proof.
intros k Hrec ly Sa U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (items & ->) Hdep
  HPRE HHEADS HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD
  Hroot Hplain Hfoot HROOM HCAP HCL HBUD.
assert (Hk : (k < 2)%nat) by (cbn [PjTree.depth] in Hdep; lia).
pose proof (Hrec Hk) as HWV.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & _ & _ & HE_gp & HE_tp & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
pose proof (fsw_sp B _ ly Sa U W regs mem md ch HPREU) as (HE_sp16 & HE_lo & _ & _).
pose proof HOUT as (HE_o8 & _ & _ & _ & _ & (HE_cap0 & _) & _).
pose proof HGLOB as (_ & _ & _ & _ & _ & _ & (HE_cnt0 & _) & _).
(* the node: an array's header, its kids block a live reader block of the tree *)
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & (Estr & Ekeys & En & Hncap & Hkc & _)).
cbn [PjTree.tag] in HH.
assert (HKB : 0 < cap0 -> 4096 + HEAD <= kids /\ kids + 56 * cap0 <= alloc_ceiling).
{ intros Hc. destruct Hkc as [(Hc0 & _) | (_ & Hin)]; [lia|].
  exact (wv_rblock_low B ly Sa W _ md mem kids (56 * cap0) HAR (HUL kids (56 * cap0) Hin)). }
(* the word at o - 8 *)
destruct (wvc_ra8_entry _ ly Sa U W regs mem md ch o ot HPRE Hoot HPRESENT HCHO) as (ra8 & H8 & HC).
pose (F := mkWF 5 pretty d ot o v str kids keys n buf cap failed text live peak cnt fail UL D (PjTree.JArr items) ra8
  (spZ regs) (2 - k)%nat).
(* the Section hypotheses of the imported steps *)
assert (HE_top47 : ly_top ly <= 2 ^ 47) by lia.
assert (HE_d : 0 <= d) by lia.
assert (HE_n : 0 <= n < 2 ^ 54).
{ destruct (Z.eq_dec cap0 0) as [Hc0|Hc0]; [lia|].
  destruct (HKB ltac:(lia)) as (K1 & K2). cbv [HEAD] in K1. lia. }
assert (HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling)).
{ change (wf_n F) with n. change (wf_kids F) with kids. change (wf_ty F) with 5. intros Hn.
  destruct (HKB ltac:(lia)) as (K1 & K2). cbv [HEAD] in K1.
  split; [lia|]. split; [lia|]. intros E; discriminate E. }
assert (HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members))).
{ left. split; [reflexivity|]. exists items. split; [reflexivity|]. split; [exact En | exact Ekeys]. }
assert (HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W mem) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn)
  by (exists num, cap0; exact HH).
assert (HE_sp : spZ regs = wf_sp F) by reflexivity.
assert (HE_pre : exists ch0, fpreU tfibsegs B (STK_write_value (wf_m F)) ly Sa U W regs mem md ch0)
  by (exists ch; exact HPRE).
assert (HULD : ublocks_ok B tfibsegs ly Sa W mem (wf_D F))
  by (intros a kk Hin; exact (HUL a kk (proj1 (HD a kk Hin)))).
(* the loop's own premises *)
assert (HWVF : write_value_spec_at B tfibsegs (S (2 - wf_m F))).
{ replace (2 - wf_m F)%nat with k; [exact HWV|]. change (wf_m F) with (2 - k)%nat. lia. }
assert (Hm12 : (1 <= wf_m F <= 2)%nat) by (change (wf_m F) with (2 - k)%nat; lia).
assert (HT : wf_t F = PjTree.JArr items) by reflexivity.
assert (HTY : wf_ty F = 5) by reflexivity.
(* the run, from the entry configuration to the spec's post *)
change (SRr tfibsegs W (cfg_at tfibsegs A_write_value regs mem md)
  (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
     (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
     regs ly Sa U W mem md)).
assert (KONT : forall W1 ms1 mdc1 ly1 S1 U1 buf1, wle W W1 ->
  wvc_invO B F ly Sa U W mem md regs W1 ms1 mdc1 ly1 S1 U1 buf1 ->
  SRr tfibsegs W1 (mkCfg ms1 mdc1)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs ly Sa U W mem md)).
{ intros W1 ms1 mdc1 ly1 S1 U1 buf1 _ HIO.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - (* the empty array: '[' then the tail put of ']' *)
    assert (Eit : items = []) by (apply length_zero_iff_nil; lia).
    assert (HWP0 : wvc_WP F = wvc_POPEN F ++ wvc_PCLOSE F).
    { change (wvc_WP F) with (WriterValue.wvpieces (PjTree.JArr items) (wvc_pp F) (wf_d F)).
      rewrite Eit. reflexivity. }
    eapply wvc_arm_empty with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
      (md0 := md) (regs0 := regs) (ly := ly1) (S := S1) (U := U1) (W := W1) (ms := ms1) (mdc := mdc1)
      (buf := buf1).
    all: assumption.
  - (* the first indent, then the item loop from item 0 *)
    assert (Hne : items <> []) by (intros E; rewrite E in En; cbn in En; lia).
    assert (Hnpos : 0 < wf_n F) by (change (wf_n F) with n; lia).
    assert (HRest : exists Rest, wvc_WP F = wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1) ++ Rest)
      by (destruct (wvc_arr_rest (wvc_pp F) d items Hne) as (Rest & ER); exists Rest; exact ER).
    assert (Hj0 : (0 < length items)%nat) by lia.
    assert (Hr0 : (length items - 0 <= length items)%nat) by lia.
    assert (KONT2 : forall W2 ms2 mdc2 ly2 S2 U2 buf2 key2, wle W1 W2 ->
      wvc_inv B F WVC_R_IND 0 (wf_keys F) key2 (wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1))
        ly Sa U W mem md regs W2 ms2 mdc2 ly2 S2 U2 buf2 ->
      SRr tfibsegs W2 (mkCfg ms2 mdc2)
        (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
           (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
           regs ly Sa U W mem md)).
    { intros W2 ms2 mdc2 ly2 S2 U2 buf2 key2 _ HI.
      assert (HI0 : wvc_inv B F WVC_R_IND (Z.of_nat 0) (wf_keys F + 8 * Z.of_nat 0) key2 (wvc_PIND_arr F items 0)
        ly Sa U W mem md regs W2 ms2 mdc2 ly2 S2 U2 buf2).
      { change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact HI. }
      eapply wvc_loop_arr with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
        (md0 := md) (regs0 := regs) (items := items) (r := length items) (j := 0%nat) (ly := ly2) (S := S2)
        (U := U2) (W := W2) (ms := ms2) (mdc := mdc2) (buf := buf2) (key := key2).
      all: assumption. }
    eapply wvc_step_open with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
      (md0 := md) (regs0 := regs) (ly := ly1) (S := S1) (U := U1) (W := W1) (ms := ms1) (mdc := mdc1)
      (buf := buf1).
    all: assumption. }
eapply wvc_step_entry with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem) (md0 := md)
  (regs0 := regs) (ch := ch).
all: assumption.
Qed.

Lemma wv_obj : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on B (fun t => exists members, t = PjTree.JObj members) k.
Proof.
intros k Hrec ly Sa U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (members & ->) Hdep
  HPRE HHEADS HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD
  Hroot Hplain Hfoot HROOM HCAP HCL HBUD.
assert (Hk : (k < 2)%nat) by (cbn [PjTree.depth] in Hdep; lia).
pose proof (Hrec Hk) as HWV.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & _ & _ & HE_gp & HE_tp & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
pose proof (fsw_sp B _ ly Sa U W regs mem md ch HPREU) as (HE_sp16 & HE_lo & _ & _).
pose proof HOUT as (HE_o8 & _ & _ & _ & _ & (HE_cap0 & _) & _).
pose proof HGLOB as (_ & _ & _ & _ & _ & _ & (HE_cnt0 & _) & _).
(* the node: an object's header, its kids and keys blocks live reader blocks of the tree *)
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & (Estr & En & Hncap & Hkc & _)).
cbn [PjTree.tag] in HH.
assert (HKB : 0 < cap0 -> (4096 + HEAD <= kids /\ kids + 56 * cap0 <= alloc_ceiling) /\
                          (4096 + HEAD <= keys /\ keys + 8 * cap0 <= alloc_ceiling)).
{ intros Hc. destruct Hkc as [(Hc0 & _) | (_ & Hin & Hin')]; [lia|].
  exact (conj (wv_rblock_low B ly Sa W _ md mem kids (56 * cap0) HAR (HUL kids (56 * cap0) Hin))
              (wv_rblock_low B ly Sa W _ md mem keys (8 * cap0) HAR (HUL keys (8 * cap0) Hin'))). }
(* the word at o - 8 *)
destruct (wvc_ra8_entry _ ly Sa U W regs mem md ch o ot HPRE Hoot HPRESENT HCHO) as (ra8 & H8 & HC).
pose (F := mkWF 6 pretty d ot o v str kids keys n buf cap failed text live peak cnt fail UL D (PjTree.JObj members) ra8
  (spZ regs) (2 - k)%nat).
(* the Section hypotheses of the imported steps *)
assert (HE_top47 : ly_top ly <= 2 ^ 47) by lia.
assert (HE_d : 0 <= d) by lia.
assert (HE_n : 0 <= n < 2 ^ 54).
{ destruct (Z.eq_dec cap0 0) as [Hc0|Hc0]; [lia|].
  destruct (HKB ltac:(lia)) as ((K1 & K2) & _). cbv [HEAD] in K1. lia. }
assert (HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling)).
{ change (wf_n F) with n. change (wf_kids F) with kids. change (wf_keys F) with keys. intros Hn.
  destruct (HKB ltac:(lia)) as ((K1 & K2) & (K3 & K4)). cbv [HEAD] in K1, K3.
  split; [lia|]. split; [lia|]. intros _. split; lia. }
assert (HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members))).
{ right. split; [reflexivity|]. exists members. split; [reflexivity | exact En]. }
assert (HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W mem) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn)
  by (exists num, cap0; exact HH).
assert (HE_sp : spZ regs = wf_sp F) by reflexivity.
assert (HE_pre : exists ch0, fpreU tfibsegs B (STK_write_value (wf_m F)) ly Sa U W regs mem md ch0)
  by (exists ch; exact HPRE).
assert (HULD : ublocks_ok B tfibsegs ly Sa W mem (wf_D F))
  by (intros a kk Hin; exact (HUL a kk (proj1 (HD a kk Hin)))).
(* the loop's own premises *)
assert (HWVF : write_value_spec_at B tfibsegs (S (2 - wf_m F))).
{ replace (2 - wf_m F)%nat with k; [exact HWV|]. change (wf_m F) with (2 - k)%nat. lia. }
assert (Hm12 : (1 <= wf_m F <= 2)%nat) by (change (wf_m F) with (2 - k)%nat; lia).
assert (HT : wf_t F = PjTree.JObj members) by reflexivity.
assert (HTY : wf_ty F = 6) by reflexivity.
(* the run, from the entry configuration to the spec's post *)
change (SRr tfibsegs W (cfg_at tfibsegs A_write_value regs mem md)
  (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
     (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
     regs ly Sa U W mem md)).
assert (KONT : forall W1 ms1 mdc1 ly1 S1 U1 buf1, wle W W1 ->
  wvc_invO B F ly Sa U W mem md regs W1 ms1 mdc1 ly1 S1 U1 buf1 ->
  SRr tfibsegs W1 (mkCfg ms1 mdc1)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs ly Sa U W mem md)).
{ intros W1 ms1 mdc1 ly1 S1 U1 buf1 _ HIO.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - (* the empty object: '{' then the tail put of '}' *)
    assert (Eit : members = []) by (apply length_zero_iff_nil; lia).
    assert (HWP0 : wvc_WP F = wvc_POPEN F ++ wvc_PCLOSE F).
    { change (wvc_WP F) with (WriterValue.wvpieces (PjTree.JObj members) (wvc_pp F) (wf_d F)).
      rewrite Eit. reflexivity. }
    eapply wvc_arm_empty with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
      (md0 := md) (regs0 := regs) (ly := ly1) (S := S1) (U := U1) (W := W1) (ms := ms1) (mdc := mdc1)
      (buf := buf1).
    all: assumption.
  - (* the first indent, then the member loop from member 0 *)
    assert (Hne : members <> []) by (intros E; rewrite E in En; cbn in En; lia).
    assert (Hnpos : 0 < wf_n F) by (change (wf_n F) with n; lia).
    assert (HRest : exists Rest, wvc_WP F = wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1) ++ Rest)
      by (destruct (wvc_obj_rest (wvc_pp F) d members Hne) as (Rest & ER); exists Rest; exact ER).
    assert (Hj0 : (0 < length members)%nat) by lia.
    assert (Hr0 : (length members - 0 <= length members)%nat) by lia.
    assert (KONT2 : forall W2 ms2 mdc2 ly2 S2 U2 buf2 key2, wle W1 W2 ->
      wvc_inv B F WVC_R_IND 0 (wf_keys F) key2 (wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1))
        ly Sa U W mem md regs W2 ms2 mdc2 ly2 S2 U2 buf2 ->
      SRr tfibsegs W2 (mkCfg ms2 mdc2)
        (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
           (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
           regs ly Sa U W mem md)).
    { intros W2 ms2 mdc2 ly2 S2 U2 buf2 key2 _ HI.
      assert (HI0 : wvc_inv B F WVC_R_IND (Z.of_nat 0) (wf_keys F + 8 * Z.of_nat 0) key2
        (wvc_PIND_obj F members 0) ly Sa U W mem md regs W2 ms2 mdc2 ly2 S2 U2 buf2).
      { change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact HI. }
      eapply wvc_loop_obj with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
        (md0 := md) (regs0 := regs) (members := members) (r := length members) (j := 0%nat) (ly := ly2)
        (S := S2) (U := U2) (W := W2) (ms := ms2) (mdc := mdc2) (buf := buf2) (key := key2).
      all: assumption. }
    eapply wvc_step_open with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem)
      (md0 := md) (regs0 := regs) (ly := ly1) (S := S1) (U := U1) (W := W1) (ms := ms1) (mdc := mdc1)
      (buf := buf1).
    all: assumption. }
eapply wvc_step_entry with (B := B) (F := F) (ly0 := ly) (S0 := Sa) (U0 := U) (W0 := W) (mem0 := mem) (md0 := md)
  (regs0 := regs) (ch := ch).
all: assumption.
Qed.

End A.
