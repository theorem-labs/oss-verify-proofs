(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment F of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a3c .. 0x86a60: the three frees of the words blocks, each pointer reloaded from the frame, and the latch), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s70.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the symbolic seed of a point of the function) and A/ACh2.v:122-290 (the step through a call and back, with the facts carried over it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* a word read through the ASan view is a 64-bit value (A's LLVMFuzzerTestOneInput_Kcut.v lt_rdword_rng) *)
Lemma ltf_aview_rng_loc : forall (segs : list Segment) H mem a b, aview segs H mem a = Some b -> 0 <= b < 256.
Proof.
intros segs H mem a b E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [x|]; cbn in E; [|discriminate].
injection E as <-. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma ltf_rdword_rng_loc : forall (segs : list Segment) H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v E. unfold rdword in E.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (ltf_aview_rng_loc _ _ _ _ _ E0). pose proof (ltf_aview_rng_loc _ _ _ _ _ E1).
pose proof (ltf_aview_rng_loc _ _ _ _ _ E2). pose proof (ltf_aview_rng_loc _ _ _ _ _ E3).
pose proof (ltf_aview_rng_loc _ _ _ _ _ E4). pose proof (ltf_aview_rng_loc _ _ _ _ _ E5).
pose proof (ltf_aview_rng_loc _ _ _ _ _ E6). pose proof (ltf_aview_rng_loc _ _ _ _ _ E7).
lia.
Qed.

(* the addresses a point of the walk reads of the recorder: the program's own statics (cmd_PG: g_rec,
   record.spill, g_quitting) and the bytes of the blocks the recorder owns *)
Definition ltf_rk (O : list (Z * Z)) (a : Z) : Prop :=
  inFP cmd_PG a \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Lemma ltf_PG_rec : forall o, 0 <= o < 960 -> inFP cmd_PG (A_G_REC + o).
Proof. intros o Ho. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma ltf_PG_spill : forall o, 0 <= o < 56 -> inFP cmd_PG (A_REC_SPILL + o).
Proof. intros o Ho. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma ltf_PG_quit : forall o, 0 <= o < 4 -> inFP cmd_PG (A_G_QUITTING + o).
Proof. intros o Ho. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the symbolic seed of the latch: every register is its own atom, atom 32 is the shadow base, no region (the
   latch makes no memory access) and no shadow entry (no inline check) *)
Definition ltf_facts : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition ltf_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None ltf_facts.
Definition ltf_Bx : sv := SOff 32 0.
Definition ltf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ltf_extra : list word := [Z_to_bv 64 SB].
Definition ltf_E (regs : bvmap 5 word) : env := Eimg (Ereg regs ltf_extra).

Lemma ltf_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (ltf_E regs) (ltf_ss pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ltf_Bx [] (ltf_E regs) (mrestrict (w_H W) mem)
  /\ img_env VAL A_LIM (ltf_E regs)
  /\ env_agree 32 (Ereg regs ltf_extra) (ltf_E regs)
  /\ (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (ltf_E regs) n = getr regs rr).
Proof.
intros W regs mem pc.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ltf_E regs) n = ew (Ereg regs ltf_extra) n)
  by (intros n Hn; unfold ltf_E; apply Eimg_low; exact Hn).
assert (E32 : ew (ltf_E regs) 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
split.
- unfold ltf_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold ltf_E. apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + apply Forall_nil.
  + first [ exact I | constructor
          | apply pairwise_disjoint_of_extents; cbn; first [exact I | constructor | repeat split] ].
  + split; [|split; [exact I | exact I]].
    cbn [ltf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- split; [apply Forall_nil|].
  split; [unfold ltf_E; apply Eimg_env|].
  split; [split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* the symbolic seed of a free (0x86a3c, 0x86a44, 0x86a4c: ld a0,off(sp); jal free): the registers are their own
   atoms, atom 32 is the frame word the step loads (8 bytes at sp + off, no inline check), held by a read-only stack
   region of one chunk; atom 2 (sp = sp1) is 16-aligned. No shadow entry. In the form of A's
   LLVMFuzzerTestOneInput_Krefusal_s1.v (kr_seed_loc). *)
Definition ltf_wrs (off : Z) : smem :=
  [YP09.mkRegion (Some 2%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))]].
Definition ltf_wfacts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ltf_wss (pc off : Z) : sstate := mkSS pc sr_atoms (ltf_wrs off) None ltf_wfacts.
Definition ltf_wBx : sv := SLit LT_SB.
Definition ltf_wBspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ltf_wE (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).

Lemma ltf_wseed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc off v,
  regions_wf (ltf_wrs off) = true ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= off <= 256 ->
  rdword (rdW W mem) (spZ regs + off) = Some v ->
  st_ok_pi SEGS VAL (ltf_wE regs v) (ltf_wss pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS ltf_wBx [] (ltf_wE regs v) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc off v Hwf Hsp Hal Hoff Hv.
set (E := ltf_wE regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 v]) n)
  by (intros n Hn; subst E; unfold ltf_wE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (ltf_rdword_rng_loc SEGS (w_H W) mem _ _ Hv) as Rv.
split.
- unfold ltf_wss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold ltf_wE. apply regs_ok_Eimg_Ereg.
  + exact Hwf.
  + unfold ltf_wrs. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (spZ regs) off 8 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ Hv).
  + unfold ltf_wrs. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [ltf_wfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    split; [|exact I]. split; [lia|]. split; [exact Hal | lia].
- unfold sh_ok. constructor.
Qed.

(* reading a callee-saved register out of aregs_preserved *)
Lemma ltf_pres_get : forall (regs regs' : bvmap 5 word) (r : Z) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rr -> getr regs' rr = getr regs rr.
Proof. intros regs regs' r rr HP Hr <-. exact (HP r Hr). Qed.

(* the bit-vector shape the latch's addiw s1,s1,1 leaves *)
Lemma ltf_addw1 : forall E (n : nat) v, ew E n = Z_to_bv 64 (Z.of_nat v) -> (v < 32)%nat ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (Z.of_nat (Datatypes.S v)).
Proof.
intros E n v Hn Hv.
assert (Hu : U E (SOff n 0) = Z.of_nat v).
{ apply U_atom; [exact Hn | lia]. }
rewrite (denot_lit_U E (SAluw ALU_ADD (SOff n 0) (SLit 1))). f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Hu, U_lit by lia.
rewrite !Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (Z.of_nat v + 1 + 2 ^ 31)) by lia.
change (bv_modulus 64) with (2 ^ 64). rewrite Nat2Z.inj_succ. rewrite Z.mod_small by lia. lia.
Qed.

(* NoDup of the live blocks and the separation of two of them, under the names this file uses *)
Lemma ltf_nodup : forall (B : asyms), AR_laws SEGS B ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros B LAWS ly S W mem md HAR.
exact (lt_ablocks_NoDup B LAWS ly S W mem md HAR).
Qed.
Lemma ltf_sep : forall (B : asyms), AR_laws SEGS B ->
  forall ly S (W : world SEGS) mem md b m p n,
  AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
  zdisjoint (b, req_size m) (p, req_size n).
Proof.
intros B LAWS ly S W mem md b m p n HAR H1 H2 Hne.
first [ exact (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne)
      | exact (sep_blocks SEGS B LAWS pa_segs_low ly S W mem md b m p n HAR H1 H2 Hne) ].
Qed.

(* ---- what one free keeps, and the state between two frees ---- *)

(* The reads the rest of the segment makes: the recorder's statics and the blocks it owns, the walk's own frame
   (from sp = x_sp1 up to the entry's sp: the ten words, the host word, the struct and the thirteen saved
   registers all lie there), and the payload's block. The 16 KB below sp are the free wrapper's own window, which
   it may write, and this segment reads nothing there. *)
Definition ltf_keep (B : asyms) (cx : lcx) (O : list (Z * Z)) (rd0 rd : reader) : Prop :=
  forall a, ltf_rk O a \/ (x_sp1 cx <= a < x_sp0 cx) \/
            (exists b n, In (b, n) (x_bl0 B cx) /\ b <= a < b + req_size n) ->
  rd a = rd0 a.
Lemma ltf_keep_refl : forall B cx O rd, ltf_keep B cx O rd rd.
Proof. intros B cx O rd a _. reflexivity. Qed.
Lemma ltf_keep_trans : forall B cx O rd0 rd1 rd2,
  ltf_keep B cx O rd0 rd1 -> ltf_keep B cx O rd1 rd2 -> ltf_keep B cx O rd0 rd2.
Proof. intros B cx O rd0 rd1 rd2 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the point between two frees: the journal from the entry, the blocks still to free, what is kept, and the
   callee-saved registers of the segment's own first state regs0 *)
Definition ltf_pt (B : asyms) (cx : lcx) (O : list (Z * Z)) (left : list (Z * Z)) (regs0 : bvmap 5 word)
  ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) (rd0 : reader) : Prop :=
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  Permutation (ablocks B ly S) (left ++ O ++ x_bl0 B cx) /\
  ltf_keep B cx O rd0 (rdW W mem) /\
  aregs_preserved regs0 regs.

(* one free: ld a0,off(sp) (the pointer from the frame word the segment's first state rd0 holds), the call of the
   free wrapper, and back at pc + 8. s0 = -1 at every program point of the loop, so the frame chain is achain's
   empty case (top - 16 <= s0). The facts of the walk are explicit arguments (RULING-STMT.md §1 names: LAWS, TL,
   the statement's AFREE4, and the record fact cmd_prog_unowned), so that the segment's own file states them once
   and applies this lemma with them. *)
Lemma ltf_free : forall (B : asyms) (MT : ameter_ops),
  AR_laws SEGS B -> PALib B -> afree04_rule SEGS B MT ->
  (forall a, inFP cmd_PG a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)) ->
  forall cx O pa n left regs0 ly S (W : world SEGS) regs mem md k rd0 (pc off : Z) Q,
  lt_base B MT cx ->
  (pc = 1292 /\ off = 120) \/ (pc = 1300 /\ off = 128) \/ (pc = 1308 /\ off = 136) ->
  ltf_pt B cx O ((pa, n) :: left) regs0 ly S W regs mem md k rd0 ->
  spZ regs0 = x_sp1 cx -> getr regs0 3 = getr (x_regs cx) 3 -> getr regs0 4 = getr (x_regs cx) 4 ->
  getr regs0 8 = w64 (-1) -> rdword rd0 (x_sp1 cx + off) = Some pa ->
  st_nev S < EV_MAX -> mo_ok MT S (mo_free MT) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     ltf_pt B cx O left regs0 ly2 S2 W2 regs2 mem2 md2 (k + 1) rd0 ->
     mo_le MT S S2 (mo_free MT) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (pc + 8))) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md) Q.
Proof.
intros B MT LAWS TL AFREE4 cmd_prog_unowned.
pose proof (paj_run B LAWS) as RUN.
intros cx O pa n left regs0 ly S W regs mem md k rd0 pc off Q HBASE Hpc HPT Hsp00 Hgp00 Htp00 H800 Hpa Hnev MOK HC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HBASE as (HPRE0 & _).
pose proof HPT as (HJ & HPerm & HK0 & HPR0).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (WS : LTOI_STK = 32768) by reflexivity.
assert (HFR : x_sp1 cx = x_sp0 cx - LT_FRAME) by reflexivity.
(* sp, gp, tp and s0 at this point, from the segment's first state *)
assert (Hsp : spZ regs = x_sp1 cx).
{ rewrite <- Hsp00. unfold spZ. f_equal.
  exact (ltf_pres_get regs0 regs 2 2%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)). }
assert (Hgp : getr regs 3 = w64 (as_gp B)).
{ exact (eq_trans (ltf_pres_get regs0 regs 3 3%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    (eq_trans Hgp00 Hgp0)). }
assert (Htp : getr regs 4 = w64 (as_tp B)).
{ exact (eq_trans (ltf_pres_get regs0 regs 4 4%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    (eq_trans Htp00 Htp0)). }
assert (H8 : getr regs 8 = w64 (-1)).
{ exact (eq_trans (ltf_pres_get regs0 regs 8 8%bv HPR0 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity))
    H800). }
(* the frame word the step loads, kept since the segment's first state *)
assert (Hoff : 120 <= off <= 136) by (destruct Hpc as [[_ ->] | [[_ ->] | [_ ->]]]; lia).
assert (Hw : rdword (rdW W mem) (spZ regs + off) = Some pa).
{ rewrite Hsp. rewrite (rdword_ext rd0 (rdW W mem) (x_sp1 cx + off)); [exact Hpa|].
  intros kk Hkk. apply HK0. right. left. rewrite HFR. unfold LT_FRAME. lia. }
assert (HspR : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite Hsp, HFR; unfold LT_FRAME; rewrite WS in Hslo; lia).
assert (Hal : spZ regs mod 16 = 0).
{ rewrite Hsp, HFR. unfold LT_FRAME. pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D. rewrite Hal16 in D.
  replace (x_sp0 cx - 256) with ((x_sp0 cx / 16 - 16) * 16) by lia. apply Z.mod_mul. lia. }
(* the block to free is live, and it is not one of the entry's *)
assert (Hin : In (pa, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPerm)). left. reflexivity. }
assert (HND : List.NoDup (ablocks B ly S)) by exact (ltf_nodup B LAWS ly S W mem md HAR).
assert (Hnb0 : ~ In (pa, n) (x_bl0 B cx)).
{ intros Hb. pose proof (Permutation_NoDup HPerm HND) as HND2. cbn [app] in HND2.
  apply NoDup_cons_iff in HND2 as [Hni _]. apply Hni. apply in_or_app. right. apply in_or_app. right. exact Hb. }
assert (HnO : ~ In (pa, n) O).
{ intros Hb. pose proof (Permutation_NoDup HPerm HND) as HND2. cbn [app] in HND2.
  apply NoDup_cons_iff in HND2 as [Hni _]. apply Hni. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (Hsp32 : 0x10000 <= x_sp1 cx) by (rewrite HFR; unfold LT_FRAME; rewrite WS in Hslo; lia).
assert (Hsp1c : alloc_ceiling <= x_sp1 cx) by (rewrite HFR; unfold LT_FRAME; rewrite WS in Hslo; lia).
assert (Hcov : In (pa, n) (ablocks B (x_ly cx) (x_S cx)) -> forall i, 0 <= i < req_size n -> inFP cmd_PG (pa + i)).
{ intros Hb. exfalso. apply Hnb0. unfold x_bl0. exact Hb. }
(* every address this segment reads is a machine address *)
assert (HBND : forall a, ltf_rk O a \/ (x_sp1 cx <= a < x_sp0 cx) \/
                 (exists b m, In (b, m) (x_bl0 B cx) /\ b <= a < b + req_size m) -> 0 <= a < 2 ^ 64).
{ intros a [[Hfp | (b & m & Hb & Hr)] | [Hs | (b & m & Hb & Hr)]].
  - destruct (cmd_prog_unowned a Hfp) as (Himg & _). pose proof (pa_img_range a Himg). lia.
  - assert (Hbl : In (b, m) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; left; exact Hb).
    destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbl) as (_ & Hb4 & Hbc & _). lia.
  - rewrite HFR in Hs. rewrite WS in Hslo. unfold LT_FRAME in Hs. lia.
  - destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) b m (proj1 HPRE0) Hb)
      as (_ & Hb4 & Hbc & _). lia. }
(* the symbolic run from pc to the free wrapper: the load of the frame word and the jal *)
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
[ destruct (ltf_wseed W regs mem 1292 120 pa ltac:(vm_compute; reflexivity) HspR Hal ltac:(lia) Hw) as [HS SHOK]
| destruct (ltf_wseed W regs mem 1300 128 pa ltac:(vm_compute; reflexivity) HspR Hal ltac:(lia) Hw) as [HS SHOK]
| destruct (ltf_wseed W regs mem 1308 136 pa ltac:(vm_compute; reflexivity) HspR Hal ltac:(lia) Hw) as [HS SHOK] ].
all: assert (HEI : img_env VAL A_LIM (ltf_wE regs pa)) by (unfold ltf_wE; apply Eimg_env).
all: assert (EL : forall n, (n < A_TEXT)%nat -> ew (ltf_wE regs pa) n = ew (Ereg regs [Z_to_bv 64 pa]) n)
       by (intros n0 Hn0; unfold ltf_wE; apply Eimg_low; exact Hn0).
all: assert (HED : ed (ltf_wE regs pa) = ed (Ereg regs [Z_to_bv 64 pa])) by reflexivity.
all: remember (ltf_wE regs pa) as E eqn:HE.
all: assert (EEo : forall n0 (rr : bv 5), Z.of_nat n0 = bv_unsigned rr -> ew E n0 = getr regs rr)
       by (intros n0 rr Hn0; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
           rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn0).
all: assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
all: assert (E32 : ew E 32 = Z_to_bv 64 pa) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
all: assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 pa]) E)
       by (split; [intros n0 Hn0; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]).
all: clear HE EL HED EEo.
all: (paj_run_tok RUN HS HJ SHOK ltf_wBspan;
      try solve [ apply awr_ok_nil
                | unfold awr_ok; intros a0 (r0 & Hin0 & Hr0); exfalso; vm_compute in Hin0;
                  destruct Hin0 as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Hr0; lia ]);
(lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end);
pmkst HS;
rewrite (pal_free B TL);
prreg HS (1%bv : bv 5) P1; prreg HS (10%bv : bv 5) P10; prreg HS (2%bv : bv 5) P2.
all: lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; lia|]); destruct Hin'
        | exact Ha | intros Hff; destruct Hff ])
end.
all: lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HPT1 : aregs_preserved regs rT)
    by (eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [Z_to_bv 64 pa] HS); [exact HAE | vm_compute; reflexivity]);
  assert (HspT : spZ rT = spZ regs) by (unfold spZ; f_equal; exact (eq_trans P2 E2));
  assert (Ha0 : getr rT 10 = w64 pa) by exact (eq_trans P10 E32);
  assert (Hgp' : getr rT 3 = w64 (as_gp B))
    by exact (eq_trans (ltf_pres_get regs rT 3 3%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Hgp);
  assert (Htp' : getr rT 4 = w64 (as_tp B))
    by exact (eq_trans (ltf_pres_get regs rT 4 4%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) Htp);
  assert (H8' : getr rT 8 = w64 (-1))
    by exact (eq_trans (ltf_pres_get regs rT 8 8%bv HPT1 ltac:(unfold acallee_saved; lia) ltac:(vm_compute; reflexivity)) H8);
  assert (HraT : YK0s.ret_ok (getr rT 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]);
  assert (Hs0 : s0Z rT = 2 ^ 64 - 1) by (unfold s0Z; rewrite H8'; vm_compute; reflexivity);
  assert (HraZ : 4096 <= raZ rT)
    by (unfold raZ; change (4096 <= bv_unsigned (getr rT (1%bv : bv 5)));
        rewrite P1; rewrite unsigned_lit_small by lia; lia);
  assert (Hch : chain_pre ly (rdW W mT) rT [])
    by (split;
        [ exact HraZ
        | destruct (frame0_ok ly rT) eqn:Hf0; [|reflexivity];
          replace (bad_next (spZ rT) (ly_top ly) (s0Z rT)) with true; [reflexivity|];
          unfold bad_next; rewrite Hs0;
          symmetry; apply orb_true_intro; left; apply orb_true_intro; right; apply Z.leb_le; rewrite Etop; lia ])
end.
all: eapply SRr_bind;
  [ lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      exact (afree04_sub SEGS B LAWS Hsegs MT AFREE4 W rT mT LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx)
        (x_W cx) (x_mem cx) (x_md cx) [] ly S dT k pa n (- LT_FRAME) (getr rT 1) [] HJ Hin Ha0
        ltac:(rewrite HspT, Hsp, HFR; unfold LT_FRAME; lia) ltac:(reflexivity) ltac:(unfold LT_FRAME; lia)
        ltac:(rewrite WS; unfold ASTACK, LT_FRAME; lia)
        Hgp' Htp' eq_refl HraT Hnev Hch Hcov MOK)
    end
  | ].
all: cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr2 & HK2 & MLE & HJin).
all: rewrite P1; apply (HC ly2 S2 W2 regs2 mem2 md2); [| exact MLE]; split; [exact HJ2|]; split;
  [ (* the blocks left *)
    apply (Permutation_app_inv_l [(pa, n)]); cbn [app];
    eapply Permutation_trans; [| exact HPerm];
    rewrite Ebl2 in *; eapply Permutation_trans; [apply Permutation_middle | rewrite <- Ebl; apply Permutation_refl]
  | split;
    [ (* what is kept *)
      intros a Ha; etransitivity; [|exact (HK0 a Ha)]; etransitivity; [|exact (KEEP a (HBND a Ha))];
      destruct HK2 as (K1 & K2 & K3 & K4 & _);
      destruct Ha as [[Hfp | (b & m & Hb & Hr)] | [Hs | (b & m & Hb & Hr)]];
      [ destruct (cmd_prog_unowned a Hfp) as (Himg & Hown & Herr); exact (K3 a Himg Hown Herr)
      | assert (Hbl : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; left; exact Hb);
        assert (Hne : (b, m) <> (pa, n)) by (intros Eq; injection Eq as -> ->; exact (HnO Hb));
        pose proof (ltf_sep B LAWS ly S W mem md b m pa n HAR Hbl Hin Hne) as Hdis;
        unfold zdisjoint in Hdis; cbn [fst snd] in Hdis;
        replace a with (b + (a - b)) by ring;
        apply (K2 b m (a - b) Hbl ltac:(lia));
        intros Hbad; cbv beta in Hbad; lia
      | apply (K1 a);
        [ lia
        | rewrite HFR in Hs; unfold ASTACK, LT_FRAME in *; lia ]
      | assert (Hbl : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HPerm)); right; apply in_or_app; right; apply in_or_app; right; exact Hb);
        assert (Hne : (b, m) <> (pa, n)) by (intros Eq; injection Eq as -> ->; exact (Hnb0 Hb));
        pose proof (ltf_sep B LAWS ly S W mem md b m pa n HAR Hbl Hin Hne) as Hdis;
        unfold zdisjoint in Hdis; cbn [fst snd] in Hdis;
        replace a with (b + (a - b)) by ring;
        apply (K2 b m (a - b) Hbl ltac:(lia));
        intros Hbad; cbv beta in Hbad; lia ]
    | exact (aregs_preserved_trans _ _ _ HPR0 (aregs_preserved_trans _ _ _ HPT1 HP2)) ] ].
Qed.

End f.
End d.
