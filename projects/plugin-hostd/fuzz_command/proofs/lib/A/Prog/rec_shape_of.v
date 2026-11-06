(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of rec_shape_of (plugin-hostd/fuzz_command, 0x891ec, 69 instructions),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the entry state with the GOT word and the shadow cell)
   and A/ACh5.v (the composition of the segments into the contract): the prologue up to the loop head (0x891ec ..
   0x89254), then the loop of lib/A/Prog/rec_shape_of_s.v for the 28 rows, from the image's read-only table g_shapes
   and the literals it points to (lib/A/Prog/CmdRo.v). The per-binary facts are the lemmas of CmdRecFacts' groups in
   lib/A/Prog/CmdRecBase.v, CmdRecRo.v and CmdRecImg.v, under the walk hypotheses
   (with cgif's names). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaSB PaDenot PaLibG CmdAddr CmdObj CmdRo
  CmdChk PaNoChain CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep rec_shape_of_c rec_shape_of_k rec_shape_of_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the read-only bytes: a word of a byte list, a prefix of an object, a string without NUL, a listed end *)
Definition le8 (l : list byte) (k : nat) : Z :=
let b j := bv_unsigned (nth (k + j) l (Z_to_bv 8 0)) in
b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))).
Lemma rdword_of_abytes : forall rd a l k, abytes_atR rd a l -> (k + 8 <= length l)%nat ->
rdword rd (a + Z.of_nat k) = Some (le8 l k).
Proof.
intros rd a l k H Hk. unfold rdword, le8.
replace (a + Z.of_nat k + 1) with (a + Z.of_nat (k + 1)) by lia.
replace (a + Z.of_nat k + 2) with (a + Z.of_nat (k + 2)) by lia.
replace (a + Z.of_nat k + 3) with (a + Z.of_nat (k + 3)) by lia.
replace (a + Z.of_nat k + 4) with (a + Z.of_nat (k + 4)) by lia.
replace (a + Z.of_nat k + 5) with (a + Z.of_nat (k + 5)) by lia.
replace (a + Z.of_nat k + 6) with (a + Z.of_nat (k + 6)) by lia.
replace (a + Z.of_nat k + 7) with (a + Z.of_nat (k + 7)) by lia.
rewrite (H k), (H (k + 1)%nat), (H (k + 2)%nat), (H (k + 3)%nat), (H (k + 4)%nat), (H (k + 5)%nat), (H (k + 6)%nat),
  (H (k + 7)%nat) by lia.
rewrite Nat.add_0_r. reflexivity.
Qed.
Lemma abytes_of_check : forall rd a l l', abytes_atR rd a l -> (length l' <= length l)%nat ->
forallb (fun i => bv_unsigned (nth i l' (Z_to_bv 8 0)) =? bv_unsigned (nth i l (Z_to_bv 8 0))) (seq 0 (length l')) = true ->
abytes_atR rd a l'.
Proof.
intros rd a l l' H Hl C i Hi. rewrite (H i) by lia. rewrite forallb_forall in C.
specialize (C i (proj2 (in_seq (length l') 0 i) ltac:(lia))). apply Z.eqb_eq in C. rewrite C. reflexivity.
Qed.
Lemma notin0 : forall s, forallb (fun b => negb (bv_unsigned b =? 0)) s = true -> ~ In (Z_to_bv 8 0) s.
Proof. intros s H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate H. Qed.
(* the value of a symbolic expression over the image's atoms (rec_shape_of_s.v's uval) *)
Ltac uval0 :=
lazymatch goal with |- sv_denot ?Ex ?e = _ => rewrite (denot_lit_U Ex e) end;
apply bv_eq; rewrite !Z_to_bv_unsigned;
rewrite ?U_SAlu; cbn [zalu_raw]; rewrite ?U_SOff, ?U_SLit;
lazymatch goal with E32 : ew _ 32 = _, E41 : ew _ 282 = _, E42 : ew _ 283 = _, E43 : ew _ 284 = _ |- _ =>
  rewrite ?E32, ?E41, ?E42, ?E43 end;
rewrite ?unsigned_lit_small by (unfold SB; lia);
vm_compute; reflexivity.
(* the object of CmdRo's read-only bytes at address a *)
Ltac ro_bytes HRO a H :=
let T := fresh "T" in pose proof HRO as T; cbv beta delta [cmd_ro_bytes] in T;
repeat lazymatch type of T with
| abytes_atR _ a _ /\ _ => apply proj1 in T
| _ /\ _ => apply proj2 in T
end;
lazymatch type of T with abytes_atR _ a _ => rename T into H end.
Ltac ro_in HROIN a H :=
let T := fresh "T" in pose proof HROIN as T; cbv beta delta [cmd_ro_in] in T;
repeat lazymatch type of T with
| (forall i, 0 <= i < _ -> _ (a + i)) /\ _ => apply proj1 in T
| _ /\ _ => apply proj2 in T
end;
lazymatch type of T with (forall i, 0 <= i < _ -> _ (a + i)) => rename T into H end.
Ltac rso_rows28 i :=
let Hc := fresh "Hc" in
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
  i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/
  i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia;
repeat (destruct Hc as [-> | Hc]); [..| subst i].
Ltac lit_str HRO a s :=
let G := fresh "G" in ro_bytes HRO a G;
split;
[ apply (abytes_of_check _ a _ _ G); [vm_compute; lia | vm_compute; reflexivity]
| apply notin0; vm_compute; reflexivity ].
(* g_shapes' rows and the strings they point to, from CmdRo's read-only bytes *)
Lemma rso_ro_of : forall rd, cmd_ro_ok rd -> rso_ro rd.
Proof.
intros rd [HRO _]. split.
- intros i Hi.
  ro_bytes HRO 0xa5ec0 G.
  assert (L : length RO_g_shapes = 448%nat) by (vm_compute; reflexivity).
  replace (0xa5ec0 + 16 * i) with (0xa5ec0 + Z.of_nat (Z.to_nat (16 * i))) by lia.
  replace (0xa5ec8 + 16 * i) with (0xa5ec0 + Z.of_nat (Z.to_nat (16 * i + 8))) by lia.
  rewrite !(rdword_of_abytes _ _ _ _ G) by (rewrite L; lia).
  rso_rows28 i.
  all: lazymatch goal with |- Some (le8 _ (Z.to_nat (16 * ?k))) = _ /\ _ =>
    let n := eval vm_compute in (rso_nm k) in let r := eval vm_compute in (rso_rp k) in
    split; [f_equal; vm_compute; reflexivity|];
    split; [f_equal; vm_compute; reflexivity|];
    change (rso_nm k) with n; change (rso_rp k) with r;
    split; [lit_str HRO n (rso_name k) | lit_str HRO r (rso_reply k)] end.
- lit_str HRO 0x21ce0 REC_MOD_HOST_SHAPE.
Qed.
(* the bytes of the 28 replies and of "resp 0" satisfy any predicate that CmdRo's objects all satisfy *)
Lemma rso_ro_in_gen : forall ro : Z -> Prop, cmd_ro_in ro ->
(forall i k, 0 <= i < 28 -> 0 <= k < astr_len (rso_reply i) + 1 -> ro (rso_rp i + k)) /\
(forall k, 0 <= k < 7 -> ro (0x21ce0 + k)).
Proof.
intros ro HROIN. split.
- intros i k Hi Hk. rso_rows28 i.
  all: lazymatch goal with |- _ (rso_rp ?j + _) =>
    let r := eval vm_compute in (rso_rp j) in let l := eval vm_compute in (astr_len (rso_reply j)) in
    change (rso_rp j) with r; change (astr_len (rso_reply j)) with l in Hk;
    let H := fresh "H" in ro_in HROIN r H; apply H; lia end.
- intros k Hk. let H := fresh "H" in ro_in HROIN 0x21ce0 H; apply H; lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the 28 names' word tails, from cmd_ro_ok's literal tails (what CmdRecFacts.v's cmd_tail_vis states) *)
Lemma rso_tails_of : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> rso_tails W mem.
Proof.
intros W mem [_ HT] i Hi a Ha. unfold cmd_ro_tails in HT.
apply (HT (rso_nm i + astr_len (rso_name i))); [|exact Ha].
rso_rows28 i; apply In_Z_of_existsb; vm_compute; reflexivity.
Qed.
(* the frame the prologue writes, from the stack region of the walk's state at the loop head: register r of
   rso_saved at offset -8 - 8 j of the entry sp *)
Lemma rso_frame_of_region : forall E m sp0 regs lo hi wlo whi cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall j r, nth_error rso_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
(forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
rso_frame m sp0 regs.
Proof.
intros E m sp0 regs lo hi wlo whi cs HR Hsp HIn HE j r Hj.
assert (Hr : 0 <= r < 32) by (apply nth_error_In in Hj; cbn in Hj; intuition lia).
pose proof (field_of_region_any E m 2 sp0 cs lo hi wlo whi _ 8 _ HR Hsp (HIn j r Hj) ltac:(lia)) as V.
cbn [sv_denot] in V. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE r Hr) in V.
rewrite Z.mod_small in V by (pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as R;
  change (bv_modulus 64) with (2 ^ 64) in R; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. exact V.
Qed.
(* the entry state: every register its own atom, atom 32 the shadow base; the regions are the 96-byte frame below
   the entry sp, the GOT word of the shadow base's cell and the cell (cgif A/AChd.v:107-108) *)
Definition rso_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).
Definition rso_entry_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_rso_entry : sstate :=
mkSS AF_rec_shape_of sr_atoms [stack_region 96; got_regionP; bcell_regionP 32] None rso_entry_facts.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches: the statement's own hypotheses, word for word (rec_shape_of_c.v:64-65),
   fx-generic; the walk uses them at the section's fx *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_bcmp).
(* the walk hypotheses: the per-binary record, the shadow base and the image facts
   (cmd_img_facts, CmdRecBase.v), from which CmdRecRo.v's RRO gives the relro range in the image and CmdRecImg.v's
   cmd_rom_view_on RtDefs.v's read-only view *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the shadow of g_shapes and of the names, from the record's checks (CmdRecBase.v's cmd_aread_ok_chk), by
   computation *)
Lemma rso_zsh_of : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> rso_zsh (rdW W mem).
Proof.
intros ly S W mem md HAR. split.
- exact (proj1 (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md 0xa5ec0 448 HAR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))).
- intros i Hi. rso_rows28 i.
  all: lazymatch goal with |- range_addressable _ _ (rso_nm ?j) ?n /\ _ =>
    exact (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md (rso_nm j) n HAR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
Qed.
(* the replies' bytes: read-only (CmdRecRo.v's cmd_ro_in_img), unowned and not the errno cell (cmd_img_facts' field
   cif_ro_unowned) *)
Lemma rso_ro_in_of : rso_ro_in B RLO RHI.
Proof.
destruct (rso_ro_in_gen _ (cmd_ro_in_img SEGS B LAWS HB IMG)) as [R1 R2].
destruct (rso_ro_in_gen _ (cif_ro_unowned _ _ IMG)) as [U1 U2].
split.
- intros i k Hi Hk. split; [exact (R1 i k Hi Hk) | exact (U1 i k Hi Hk)].
- intros k Hk. split; [exact (R2 k Hk) | exact (U2 k Hk)].
Qed.
Let RUNTO := paj_run_to B LAWS.
Lemma rso_entry_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md,
AR SEGS B ly S W mem md -> astk_ok REC_SHAPE_OF_STK ly (spZ regs) ->
(forall a, spZ regs - REC_SHAPE_OF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (rso_E0 regs) ss_rso_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rec_shape_of)) mem (seg_rom SEGS)))
/\ sh_ok SEGS RBx [] (rso_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md HAR Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_SHAPE_OF_STK = 8288) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
set (E := rso_E0 regs).
assert (E2 : ew E 2 = getr regs 2).
{ subst E. unfold rso_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold rso_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold rso_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold rso_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rso_entry. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold rso_E0. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r, SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rso_entry_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok. apply Forall_nil.
Qed.
(* 0x891ec .. 0x89254: the frame, the eleven saved registers, s0 := len, s1 := the verb, the table's address, the
   shadow base and the loop counters; then the loop from row 0 *)
Lemma rso_entry_ok : forall ly S W (regs : bvmap 5 word) mem md p v,
rso_cx B RLO RHI ly S W regs mem md p v -> rt_rom_view SEGS B W mem ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_shape_of) regs mem md) (rso_post B RLO RHI ly S W regs mem md v).
Proof.
intros ly S W regs mem md p v CX RV.
pose proof rso_zsh_of as RZ.
pose proof (ASTRLEN fx) as ASTRLENx. pose proof (ABCMP fx) as ABCMPx.
assert (H0 : HEAD_stmt B RLO RHI 0) by (eapply rso_heads_all; try eassumption; lia).
pose proof CX as (HPRE & H10 & H11 & HVO & HRO & HROIN & HTAIL & HVERB & HGAP).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_SHAPE_OF_STK = 8288) by reflexivity.
destruct (rso_val_objs HVO) as (V41 & V42 & V43).
destruct (rso_entry_seed W regs mem ly S md HAR Hstk Hpres) as [HS SHOK].
pose proof (ajournal_init_na SEGS B REC_SHAPE_OF_STK [] ly S W regs mem md HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (rso_E0 regs)) by (unfold rso_E0; apply Eimg_env).
set (E := rso_E0 regs) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. unfold rso_E0. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold rso_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E41 : ew E 282 = Z_to_bv 64 0xa5ec0) by (subst E; unfold rso_E0; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 282%nat with (A_OBJ 41); rewrite V41; reflexivity).
assert (E42 : ew E 283 = Z_to_bv 64 0x21ce0) by (subst E; unfold rso_E0; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 283%nat with (A_OBJ 42); rewrite V42; reflexivity).
assert (E43 : ew E 284 = Z_to_bv 64 0xa5ec8) by (subst E; unfold rso_E0; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 284%nat with (A_OBJ 43); rewrite V43; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at.
paj_run_to_tok RUNTO HS HJ SHOK RBspan RS_HEAD.
{ awr_ok_tac. exact Usp. }
pmkst HS.
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem) (mrestrict _ ?mm) |- _ =>
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REC_SHAPE_OF_STK <= a < spZ regs) ->
  aview SEGS (w_H W) mm a = aview SEGS (w_H W) mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - REC_SHAPE_OF_STK <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; try rewrite Usp in Hrr; rewrite WS; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0 end.
pose proof (rso_frame_of_region E _ (spZ regs) regs _ _ _ _ _ HR0 Usp
  ltac:(intros j r Hj; do 11 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right]) |]);
        cbn in Hj; destruct j; discriminate Hj)
  ltac:(intros r Hr; subst E; unfold rso_E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat;
        rewrite Z2Nat.id by lia; symmetry; apply Z_to_bv_small; change (bv_modulus 5) with 32; lia)) as HFR.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (HLm : rso_low W mem mm) by (intros a Ha; apply KEEP; [lia | unfold REC_SHAPE_OF_STK, ESTACK in *; lia]);
  apply (H0 ly S W regs mem md p v rg mm mdq CX) end.
- split; [exact HJ|]. split; [exact KEEP | exact HFR].
- unfold rso_regs_at. repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with |- getr _ ?k = _ =>
    let Q := fresh "Q" in rawreg HS k Q; rewrite Q; clear Q;
    first
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EE; reflexivity
    | cbn [sv_denot]; rewrite Usp; unfold w64; f_equal; lia
    | uval0 ] end.
- intros j Hj. lia.
- exact (low_rt_rom W mem _ HLm RV).
Qed.
(* the contract, exactly as rec_shape_of_c.v states it *)
Theorem trec_shape_of_spec_holds : trec_shape_of_spec B MT.
Proof.
intros ly S W regs mem md p v HPRE HROD H10 Hp H11 Hlen HRO HVO HVERB HEV.
apply (rso_entry_ok ly S W regs mem md p v); [|exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W mem HROD)].
split; [exact HPRE|]. split; [exact H10|]. split; [exact H11|]. split; [exact HVO|].
split; [exact (rso_ro_of _ HRO)|]. split; [exact rso_ro_in_of|].
split; [exact (rso_tails_of W mem HRO)|].
split; [exact HVERB|].
split; [exact (RRO SEGS B LAWS HB IMG) | exact Hlen].
Qed.
End e.
End f.
End d.
