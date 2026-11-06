(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Case 3 of the B walk of LLVMFuzzerTestOneInput, segment A: from the cut LI_T (0x8034c) to the point C3_RN
   (0x80828, read_name has returned); BoxBLxCase3Defs.v holds the points and the seat.
   The code: the switch (0x8034c .. 0x803d0, two branches that op & 3 = 3 decides), case 3 at 0x804d0, the inlined
   fuzz_u8 that reads the index byte (0x804d0 .. 0x80504 when the input has a byte left, 0x8081c when it has none),
   and read_name (&in) at 0x80824 (BoxBReadName.v, caller-journal form).
   - With a byte left (c3A_seat), the runs stop at read_name's entry with the index byte in s8 and the cursor
     advanced by one; with the input used up (c3A0_seat: the cursor's n is 0), `beqz` 0x804d4 goes to 0x8081c and
     s8 = 0.
   - At the entry, the cut's facts are read back from the engine's state (lx_land and the spill region's chunks;
     the runs write only the spill window [sp1, sp1 + 152), so frame_of keeps the registry, prev and the input:
     c3a_kept_win), and c3a_call applies HY's lh_read_name: its post adds the name block (s, rn_k pl + 1), advances
     the cursor and keeps every other byte the cut speaks about (tbcj_kept, across the post's world: c3a_kat), and
     the state at the return address 0x80828 is C3_RN. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReadName BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase3Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd printf_facts_c read_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* The write rights of every run of this segment: only the spill region has a window. *)
Ltac c3_awr_run EA2 :=
  eapply c3_awr_gen; [exact EA2 | lia | lia |];
  repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.r_whi YP09.r_wlo YP09.r_base];
  first [left; lia | right; split; [reflexivity | split; unfold LX_STK; lia]].


Lemma c3a_rdw : forall (H H2 : word -> bool) m m2 a v,
  (forall j, 0 <= j < 8 -> aview SEGS H2 m2 (a + j) = aview SEGS H m (a + j)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H2 m2) a = Some v.
Proof.
  intros H H2 m m2 a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma c3a_pw_last : forall {X} (R : X -> X -> Prop) l x y, pairwise R (l ++ [x]) -> In y l -> R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hy; [destruct Hy|].
  cbn [app pairwise] in H. destruct H as [Hf Hp]. destruct Hy as [<- | Hy].
  - rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. left. reflexivity.
  - exact (IH x y Hp Hy).
Qed.

Lemma c3a_rnk : forall pl, 0 <= read_name_c.rn_k pl <= 47 /\
  read_name_c.rn_k pl + Z.min (Z.of_nat (length pl)) 1 <= Z.of_nat (length pl) /\
  length (Boxreg.bsub pl 1 (read_name_c.rn_k pl)) = Z.to_nat (read_name_c.rn_k pl).
Proof.
  intros [|x rest]; cbn [read_name_c.rn_k length].
  - split; [lia|]. split; [cbn; lia|]. reflexivity.
  - pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)) as Hm.
    split; [lia|]. split; [lia|].
    unfold Boxreg.bsub. change (Z.to_nat 1) with 1%nat. cbn [skipn]. rewrite skipn_O.
    rewrite length_firstn. lia.
Qed.

Lemma c3a_shape : forall pc (W : world SEGS) ms,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros pc W ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
  destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
  subst. reflexivity.
Qed.

Definition c3a_kat (cx : lxcx) (fp r a : Z) : Prop :=
  lsp1 cx <= a < lsp1 cx + 0x88 \/ lsp1 cx + 0x98 <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/
  lF cx fp <= a < lF cx fp + 512 \/ lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288.

(* A run's frame_of keeps every byte outside the spill window [x, x + 152) when that is the only write window. *)
Definition c3a_win_ok (w : option nat * Z * Z) : bool :=
  let '(b, wlo, whi) := w in
  (whi <=? wlo) || (match b with Some n => Nat.eqb n 2 | None => false end && (0 <=? wlo) && (whi <=? 152)).

Lemma c3a_kept_win : forall E rs H m m' x,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb c3a_win_ok (windows rs) = true ->
  YP09.base_val E (Some LA_SP) = x ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (x <= a < x + 152) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' x HF Hw Hx a Ha Hn.
  apply (kept_of_frame E rs H m m' (fun a0 => x <= a0 < x + 152) HF); [|exact Ha|exact Hn].
  intros b wlo whi a0 Hin Hr. rewrite forallb_forall in Hw. specialize (Hw _ Hin). unfold c3a_win_ok in Hw.
  apply orb_true_iff in Hw as [Hw | Hw]; [apply Z.leb_le in Hw; lia|].
  apply andb_true_iff in Hw as [Hw H2]. apply andb_true_iff in Hw as [Hb H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct b as [n|]; [|discriminate Hb]. apply Nat.eqb_eq in Hb. subst n. unfold LA_SP in Hx. rewrite Hx in Hr. lia.
Qed.

Lemma c3a_rdword_range : forall (H : word -> bool) mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H mem a v Hr. unfold rdword in Hr.
  repeat match type of Hr with context [aview SEGS H mem ?x] =>
    let b := fresh "b" in let Eb := fresh "Eb" in
    destruct (aview SEGS H mem x) as [b|] eqn:Eb; [|discriminate Hr];
    destruct (aview_byte SEGS H mem x b Eb) as (? & _ & _ & ?) end.
  injection Hr as <-. lia.
Qed.

Lemma c3a_den_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

Ltac c3_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* The seat of the used-up path (the cursor at the input's end): no byte region, atom 49 (n - S pos) is 0. *)
Definition c3A0_G : facts := mkFacts (LX_AF ++ [(49%nat, mkAF 0 0 0)]) [] [].

Lemma c3A0_seat : forall cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lx_body cx fp LP_T W3 ms3 LSH_iter -> lblk B cx ly3 S3 r -> Boxreg.boxreg_inv bs -> Boxreg.bx_fabric bs = fab ->
  S pos = length (lc_pl cx) -> lcur cx W3 ms3 (S pos) -> lslots_loop cx fp W3 ms3 r fab ->
  getr (ms_regs ms3) 19 = w64 1 -> getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms3) 27 = w64 fab ->
  E = lx_env cx fp (ms_regs ms3) (c3A_ex cx fp r pos) ->
  st_ok_pi SEGS VAL E (lx_ss LP_T (lx_sr c3A_ov) LSH_iter (lx_slot_chunks c3A_l) [] 0 0 0 0 [] c3A0_G)
    (restrict (w_H W3) ms3).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E HB HJ HFR HBD Hblk Hinv Hfab Hlen Hcur Hloop R19 R20 R21 R27 HEdef.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & HRG & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_sp_facts B MT cx HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof HJ as (HAR3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (_ & _ & _ & Hpn & _).
  destruct Hpn as [Hn0 | (Hnpos & Hin0)]; [unfold lc_n in Hn0; lia|].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
  rewrite (c3_req (lc_n cx)) in Hpceil, Hpia by lia.
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  pose proof Hcur as (Hcl & H88 & H90).
  pose proof Hloop as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  pose proof Hinv as ((_ & _ & HB2 & _) & _). unfold Boxreg.boxreg_B2 in HB2.
  assert (HE : lx_E cx fp E) by (rewrite HEdef; apply lx_env_E; exact HRG).
  pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESV & E46 & E47).
  assert (EX : forall j, (j < 6)%nat -> ew E (LA_EX + j) = nth j (c3A_ex cx fp r pos) (w64 0))
    by (intros j Hj; rewrite HEdef; apply lx_env_ex; unfold LA_EX; lia).
  pose proof (EX 0%nat ltac:(lia)) as E48. pose proof (EX 1%nat ltac:(lia)) as E49.
  pose proof (EX 2%nat ltac:(lia)) as E50. pose proof (EX 3%nat ltac:(lia)) as E51.
  pose proof (EX 4%nat ltac:(lia)) as E52.
  cbn [nth c3A_ex LA_EX Nat.add] in E48, E49, E50, E51, E52.
  assert (E20 : ew E 20 = w64 r)
    by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 20 (20%bv : bv 5)) by reflexivity; exact R20).
  assert (E27 : ew E 27 = w64 fab)
    by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 27 (27%bv : bv 5)) by reflexivity; exact R27).
  assert (Hshr : 0 <= shadow_addr (r + 280) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (Hn0 : lc_n cx - Z.of_nat (S pos) = 0) by (unfold lc_n; lia).
  apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E LP_T (lx_sr c3A_ov) LSH_iter c3A_l [] 0 0 0 0
           [] c3A0_G HE HBD).
  - apply lx_regs_ok; [rewrite HEdef; apply lx_regs_ok_atoms|]. unfold c3A_ov. apply Forall_app. split.
    + rewrite HEdef. apply lx_ovp_ok; [exact HRG | exact R21].
    + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd sv_denot]. rewrite R19. reflexivity.
  - unfold c3A_l, lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + exact (lx_slot_lit cx W3 ms3 E 8 3 L08 ltac:(lia)).
    + apply (lx_slot_atom cx W3 ms3 E 16 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S10 | exact E46 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 24 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S18 | exact E46 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 40 20 r 280); [exact L28 | exact E20 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 48 27 fab 0); [rewrite Z.add_0_r; exact L30 | exact E27 | lia | lia].
    + exact (lx_slot_lit cx W3 ms3 E 56 0 L38 ltac:(lia)).
    + apply (lx_slot_atom cx W3 ms3 E 64 50 (shadow_addr (r + 280)) 0); [rewrite Z.add_0_r; exact L40 | exact E50 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 104 LA_F (lF cx fp) 32); [exact L68 | exact E46 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 112 51 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact E51 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 120 52 (2 ^ 64 - 1 - (lF cx fp + 64)) 0);
        [rewrite Z.add_0_r; exact L78 | exact E52 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 128 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact S80 | exact E46 | lia | lia].
    + apply (lx_slot_atom cx W3 ms3 E 136 48 (lc_p cx + Z.of_nat (S pos)) 0);
        [rewrite Z.add_0_r; exact H88 | exact E48 | unfold lc_n in *; lia | unfold lc_n in *; lia].
    + apply (lx_slot_atom cx W3 ms3 E 144 49 (lc_n cx - Z.of_nat (S pos)) 0);
        [rewrite Z.add_0_r; exact H90 | exact E49 | lia | lia].
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [YP09.pairwise_disjoint]. exact I.
  - unfold lx_regions0. repeat apply Forall_cons; try apply Forall_nil; exact I.
  - unfold c3A0_G. split; [|split; exact I]. cbn [f_atoms].
    apply c3_atoms_ok_app; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE)|].
    cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E49, Hn0. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- read_name's call at 0x80824 and the landing on C3_RN ---- *)

Section rn.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Hypothesis HRN : lx_from B MT POST (C3_RN B MT i).

Lemma c3a_call : forall cx fp k acc ly3 S3 W3 (ms : machine_state) md (P : nat) r fab op idxb bs,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  0 < lc_n cx -> frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  lblk B cx ly3 S3 r -> Boxreg.boxreg_inv bs -> Boxreg.bx_fabric bs = fab ->
  Z.land op 3 = 3 -> 0 <= op < 256 -> 0 <= idxb < 256 ->
  lx_body cx fp AF_read_name W3 ms LSH_iter ->
  lreg W3 ms r bs -> lprev cx fp W3 ms bs -> lcur cx W3 ms P -> lslots_loop cx fp W3 ms r fab ->
  lslot cx W3 ms 0x58 (Z.of_nat i) ->
  getr (ms_regs ms) 1 = w64 (BASE + LP_RN) -> getr (ms_regs ms) 10 = w64 (lsp1 cx + 0x88) ->
  getr (ms_regs ms) 19 = w64 1 -> getr (ms_regs ms) 20 = w64 r ->
  getr (ms_regs ms) 21 = w64 (lF cx fp + 64) -> getr (ms_regs ms) 23 = w64 op ->
  getr (ms_regs ms) 24 = w64 idxb -> getr (ms_regs ms) 26 = w64 (Boxreg.bx_n bs) ->
  getr (ms_regs ms) 27 = w64 fab ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros cx fp k acc ly3 S3 W3 ms md P r fab op idxb bs HB HJ Hn0 HFR HLE Hi Hk Hacc Hblk Hinv Hfab Hop3 Hop Hidx
    HBD Hreg Hprev Hcur Hloop S58 R1 R10 R19 R20 R21 R23 R24 R26 R27.
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & S10 & S18 & S80 & HINP).
  pose proof HREGS as (L2 & L8 & L9 & L3 & L4 & L18 & L22).
  pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPceil & SP47 & SPsp1 & SPal).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ) as EFA.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & _ & _ & HROD & _).
  pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & _).
  pose proof HJ as (HAR3 & _).
  pose proof Hcur as (HPle & C88 & C90).
  destruct Hpn as [Hpn | (_ & Hinc)]; [lia|].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hinc).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
  rewrite (c3_req (lc_n cx)) in Hpceil by lia.
  assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3)) by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin3) as (_ & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  assert (Hsp : spZ (ms_regs ms) = lsp1 cx) by (unfold spZ; rewrite L2; apply unsigned_lit_small; lia).
  assert (Hsp32 : exists t, lsp1 cx = 32 * t) by (exists (lsp1 cx / 32); pose proof (Z.div_mod (lsp1 cx) 32 ltac:(lia)); lia).
  destruct Hsp32 as (t & Ht).
  set (pl := skipn P (lc_pl cx)).
  assert (Hlen : Z.of_nat (length pl) = lc_n cx - Z.of_nat P) by (subst pl; rewrite length_skipn; unfold lc_n; lia).
  pose proof (c3a_rnk pl) as (Hk47 & Hused & Hnml).
  assert (Hshape : mkCfg ms md = cfg_at SEGS AB_read_nameP (ms_regs ms) (ms_mem ms) md).
  { unfold cfg_at, AB_read_nameP. rewrite (c3a_shape AF_read_name W3 ms Hpc Hresv Hsvc Hrom Hfreg Hfcsr) at 1. reflexivity. }
  rewrite Hshape.

  assert (P1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; unfold LP_RN; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (P2 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite R1; unfold w64, LP_RN; rewrite unsigned_lit_small by lia; lia).
  assert (P3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite L3; exact Hgp).
  assert (P4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite L4; exact Htp).
  assert (P5 : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp, Ht; replace (32 * t) with ((2 * t) * 16) by lia; apply Z_mod_mult).
  assert (P6 : lsp0 cx - LX_STK <= spZ (ms_regs ms) - READ_NAME_STKB) by (rewrite Hsp; unfold READ_NAME_STKB, ASTACK, LX_STK; lia).
  assert (P7 : spZ (ms_regs ms) <= lsp0 cx) by lia.
  assert (P9 : (lsp1 cx + 0x88) mod 8 = 0) by (rewrite Ht; replace (32 * t + 0x88) with ((4 * t + 17) * 8) by lia; apply Z_mod_mult).
  assert (P10 : spZ (ms_regs ms) <= lsp1 cx + 0x88) by lia.
  assert (P11 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (lsp1 cx + 0x88) 8 (lc_p cx + Z.of_nat P))
    by exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms) _ _ C88).
  assert (P12 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (lsp1 cx + 0x88 + 8) 8 (Z.of_nat (length pl)))
    by (rewrite Hlen; replace (lsp1 cx + 0x88 + 8) with (lsp1 cx + 0x90) by lia;
        exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms) _ _ C90)).
  assert (WIN : forall a, lsp1 cx + 0x88 <= a < lsp1 cx + 0x88 + 16 ->
    awr_byte LX_STK (lsp0 cx) [] (ablocks B (lc_ly cx) (lc_S cx)) (ablocks B ly3 S3) ly3 [(LX_CID, fp)] a /\
    apresent (w_H W3) (ms_mem ms) a /\ ~ aowned B ly3 S3 a /\ ly_stk_lo ly3 <= a < ly_stk_hi ly3)
    by (intros a Ha; apply (c3_stack_win B MT HY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ); unfold LX_STK; lia).
  assert (P13 : range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (lsp1 cx + 0x88) 16).
  { destruct (WIN (lsp1 cx + 0x88) ltac:(lia)) as (_ & _ & _ & Wl & _).
    destruct (WIN (lsp1 cx + 0x88 + 15) ltac:(lia)) as (_ & _ & _ & _ & Wh).
    exact (c3_stk_ra B MT HY ly3 S3 W3 (ms_mem ms) _ (lsp1 cx + 0x88) 16 HAR3 Wl ltac:(lia)). }
  assert (P14 : tbwr_ok B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) ly3 S3 [(LX_CID, fp)] W3 (ms_mem ms)
                  (spZ (ms_regs ms)) (lsp1 cx + 0x88) 16).
  { intros a Ha. destruct (WIN a Ha) as (Wa & Wp & Wo & _). split; [exact Wa|]. split; [exact Wp|]. split; [exact Wo|].
    rewrite Hsp. lia. }

  assert (P15 : 0 <= lc_p cx + Z.of_nat P) by lia.
  assert (P16 : lc_p cx + Z.of_nat P + Z.of_nat (length pl) <= 2 ^ 63) by lia.
  assert (P17 : amem_range (lc_p cx + Z.of_nat P) (Z.of_nat (length pl)))
    by (apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) md (lc_p cx) (lc_n cx)); [exact HAR3 | exact Hin3 | lia | rewrite c3_req by lia; lia]).
  assert (P18 : pl <> [] -> In (lc_p cx, lc_n cx) (ablocks B ly3 S3) /\ lc_p cx <= lc_p cx + Z.of_nat P /\
                lc_p cx + Z.of_nat P + Z.of_nat (length pl) <= lc_p cx + lc_n cx)
    by (intros _; split; [exact Hin3 | lia]).
  assert (P19 : forall j, 0 <= j < Z.of_nat (length pl) ->
    aview SEGS (w_H W3) (ms_mem ms) (lc_p cx + Z.of_nat P + j) = Some (bv_unsigned (nth (Z.to_nat j) pl (Z_to_bv 8 0)))).
  { intros j Hj. subst pl. rewrite nth_skipn.
    replace (lc_p cx + Z.of_nat P + j) with (lc_p cx + Z.of_nat (P + Z.to_nat j)) by lia.
    replace (P + Z.to_nat j)%nat with (Z.to_nat (Z.of_nat (P + Z.to_nat j))) at 2 by lia.
    apply (c3_garr8_view W3 (ms_mem ms) (lc_p cx) (lc_pl cx) _ HINP). unfold lc_n in Hlen. lia. }
  destruct (c3_room B MT HY cx fp k acc ly3 S3 W3 (ms_mem ms) md r i (read_name_c.rn_k pl + 1) HB HJ HLE Hblk Hk Hi Hacc
              ltac:(lia)) as (P20 & P21 & P22 & Pacc).
  eapply SRr_bind.
  { exact (lh_read_name B MT HY LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
      [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k (ms_regs ms) (lsp1 cx + 0x88) (lc_p cx + Z.of_nat P) (lc_p cx) (lc_n cx) pl
      HJ P1 P2 P3 P4 P5 P6 P7 R10 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 (lh_rn_trace B MT HY)). }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & s & -> & HJ2 & HP & R10s & HFR2 & Hs & HBL2 & _ & _ & HNM
    & HC0 & HC8 & HMO2 & HKC).

  pose proof HJ2 as (HAR2 & _).
  assert (Hsin2 : In (s, read_name_c.rn_k pl + 1) (ablocks B ly2 S2))
    by (rewrite HBL2; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hsin2) as (_ & _ & Hsceil & Hsia & _ & Hpw2 & _).
  rewrite (c3_req (read_name_c.rn_k pl + 1)) in Hsceil, Hsia by lia.
  assert (Hpw : forall b n, In (b, n) (ablocks B ly3 S3) ->
    b + req_size n <= s \/ s + (read_name_c.rn_k pl + 1) <= b).
  { intros b n Hb. rewrite HBL2, map_app in Hpw2. cbn [map] in Hpw2.
    pose proof (c3a_pw_last zdisjoint _ _ _ Hpw2 (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ Hb)) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite (c3_req (read_name_c.rn_k pl + 1)) in Hz by lia. exact Hz. }
  assert (HFR2' : frames S2 = [(LX_CID, fp)]) by (rewrite HFR2; exact HFR).
  assert (EFA2 : frame_addr ly2 LX_CID fp = lF cx fp)
    by exact (lx_frame_addr_eq B MT LAWS cx fp W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) ly2 S2 md2 _ HB HJ2).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp HAR2 Hsin2 (lx_fin fp S2 HFR2')) as HsF.
  unfold zdisjoint in HsF. cbn [fst snd] in HsF. rewrite EFA2, (c3_req (read_name_c.rn_k pl + 1)) in HsF by lia.
  change (fs_frame_bytes LX_CID) with 512 in HsF.
  pose proof (Hpw _ _ Hin3) as Hsp3. rewrite (c3_req (lc_n cx)) in Hsp3 by lia.
  pose proof (Hpw _ _ Hrin3) as Hsr3. change (req_size LX_REG) with 288 in Hsr3.
  (* the frame's shadow lies in the shadow band, apart from the name block and below the ceiling *)
  assert (HSHx : SHADOW_OFF + 512 <= lSH cx fp /\ lSH cx fp + 64 <= 17594333495295).
  { rewrite HSHeq. clear - HF0 HFc CC1. unfold SHADOW_OFF. lia. }
  assert (HshS : lSH cx fp + 64 <= s \/ s + (read_name_c.rn_k pl + 1) <= lSH cx fp)
    by (clear - Hsia HSHx CC3; unfold in_app, kLowShadowBeg, SHADOW_OFF in *; lia).
  assert (HSHc : lSH cx fp + 64 <= alloc_ceiling) by (clear - HSHx CC1; lia).
  clear SP16 SPal HF64 HSHeq P5 P9 HBASE HSHx.
  assert (NWc : forall a, c3a_kat cx fp r a -> ~ read_name_c.rn_writes (lsp1 cx + 0x88) s (read_name_c.rn_k pl) a).
  { clear - Hsp3 Hsr3 HsF HshS HSHc Hsceil Hpceil Hrceil HFc SPceil SPsp1 HF0.
    intros a Ha HW. unfold c3a_kat, read_name_c.rn_writes in *. lia. }
  assert (KP : forall a, c3a_kat cx fp r a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. pose proof HKC as (K1 & K2 & _ & K4 & _). rewrite Hsp in K1.
    pose proof (NWc a Ha) as NW.
    unfold c3a_kat in Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
    - apply K1; [lia | unfold READ_NAME_STKB, ASTACK; lia | exact NW].
    - apply K1; [lia | unfold READ_NAME_STKB, ASTACK; lia | exact NW].
    - replace a with (lc_p cx + (a - lc_p cx)) in NW |- * by lia.
      apply (K2 _ _ _ Hin3); [rewrite c3_req by lia; lia | exact NW].
    - apply (K4 LX_CID fp a (lx_fin fp S3 HFR)); [|exact NW].
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes LX_CID) with 512. lia.
    - apply (K4 LX_CID fp a (lx_fin fp S3 HFR)); [|exact NW].
      right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes LX_CID / 8) with 64.
      change (shadow_addr (lF cx fp)) with (lSH cx fp). lia.
    - replace a with (r + (a - r)) in NW |- * by lia.
      apply (K2 _ _ _ Hrin3); [change (req_size LX_REG) with 288; lia | exact NW]. }

  assert (RDK : forall a v, (forall j, 0 <= j < 8 -> c3a_kat cx fp r (a + j)) ->
    rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v -> rdword (aview SEGS (w_H W2) mem2) a = Some v)
    by (intros a v Ha Hr; apply (c3a_rdw (w_H W3) (w_H W2) (ms_mem ms) mem2 a v); [intros j Hj; apply KP, Ha, Hj | exact Hr]).
  assert (SLK : forall off v, 0 <= off -> off + 8 <= 0x88 -> lslot cx W3 ms off v ->
    rdword (aview SEGS (w_H W2) mem2) (lsp1 cx + off) = Some v)
    by (intros off v H0 H1 Hv; apply RDK; [intros j Hj; unfold c3a_kat; lia | exact Hv]).
  apply (HRN cx fp (k + EV_READ_NAMEB) (acc + mo_malloc MT (read_name_c.rn_k pl + 1)) ly2 S2 W2
           (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR2'
           (mle_station MT _ _ _ _ _ (lh_mtl B MT HY) HLE HMO2)).
  unfold C3_RN.
  exists (P + Z.to_nat (tbread_name_used pl))%nat, r, fab, op, idxb, s, bs, (Boxreg.bsub pl 1 (read_name_c.rn_k pl)).
  unfold C3_body, c3_nlen. rewrite Hnml, Z2Nat.id by lia.
  unfold lx_body, lregs, lsaved, lshadow, lslot, lreg, lprev, lcur, lslots_loop, lview.
  cbn [ms_regs ms_mem ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].

  unfold lslot, lview. cbn [ms_mem].
  assert (RG : forall x : Z, acallee_saved x -> forall v, getr (ms_regs ms) (Z_to_bv 5 x) = v -> getr regs2 (Z_to_bv 5 x) = v)
    by (intros x Hx v Hv; rewrite (HP x Hx); exact Hv).
  pose proof HSAVED as (Hra & Hsj).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (HU : 0 <= tbread_name_used pl) by (unfold tbread_name_used; lia).
  assert (HU2 : tbread_name_used pl <= lc_n cx - Z.of_nat P) by (unfold tbread_name_used; lia).
  pose proof Hloop as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  split; [split|].
  - split; [exact R1|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [exact (RG 2 ltac:(unfold acallee_saved; lia) _ L2)|].
      split; [exact (RG 8 ltac:(unfold acallee_saved; lia) _ L8)|].
      split; [exact (RG 9 ltac:(unfold acallee_saved; lia) _ L9)|].
      split; [exact (RG 3 ltac:(unfold acallee_saved; lia) _ L3)|].
      split; [exact (RG 4 ltac:(unfold acallee_saved; lia) _ L4)|].
      split; [exact (RG 18 ltac:(unfold acallee_saved; lia) _ L18)|].
      exact (RG 22 ltac:(unfold acallee_saved; lia) _ L22). }
    split.
    { split.
      - apply RDK; [intros j Hj; unfold c3a_kat; lia | exact Hra].
      - intros j Hj. apply RDK; [intros j' Hj'; unfold c3a_kat; lia | exact (Hsj j Hj)]. }
    split.
    { intros j Hj. rewrite KP; [exact (HSH j Hj)|]. unfold c3a_kat. change (length LSH_iter) with 52%nat in Hj. lia. }
    split.
    { rewrite Hfb in *. apply RDK; [intros j Hj; unfold c3a_kat; lia | exact HFLAG]. }
    split; [exact (SLK 16 _ ltac:(lia) ltac:(lia) S10)|].
    split; [exact (SLK 24 _ ltac:(lia) ltac:(lia) S18)|].
    split; [exact (SLK 128 _ ltac:(lia) ltac:(lia) S80)|].
    intros j Hj. destruct (HINP j Hj) as [Hv Hb]. split; [|exact Hb].
    intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
    pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
    rewrite length_map in Hj.
    rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W2) (ms_mem ms) mem2 _ (KP (lc_p cx + Z.of_nat j) ltac:(unfold c3a_kat, lc_n; lia))).
    exact Hv0.
  - split; [exact Hi|].
    split; [unfold EV_READ_NAMEB; lia|].
    split; [lia|].
    split; [rewrite HBL2; unfold lblk in Hblk; rewrite Hblk, <- app_assoc; reflexivity|].
    split; [exact Hs|].
    split; [lia|].
    split; [exact HNM|].
    split; [intros j Hj; rewrite KP; [exact (Hreg j Hj) | unfold c3a_kat, LX_REG in *; lia]|].
    split; [exact Hinv|]. split; [exact Hfab|].
    split; [intros j Hj; rewrite KP; [exact (Hprev j Hj) | unfold c3a_kat, LX_REG in *; lia]|].
    split; [exact Hop3|]. split; [exact Hop|].
    split.
    { split; [unfold lc_n in HU2; lia|]. split.
      - apply rdword_of_val_mem; [|lia].
        replace (lc_p cx + Z.of_nat (P + Z.to_nat (tbread_name_used pl))) with (lc_p cx + Z.of_nat P + tbread_name_used pl) by lia.
        exact HC0.
      - apply rdword_of_val_mem; [|lia].
        replace (lc_n cx - Z.of_nat (P + Z.to_nat (tbread_name_used pl))) with (Z.of_nat (length pl) - tbread_name_used pl) by lia.
        replace (lsp1 cx + 144) with (lsp1 cx + 0x88 + 8) by lia. exact HC8. }
    split.
    { split; [exact (SLK 8 _ ltac:(lia) ltac:(lia) L08)|]. split; [exact (SLK 40 _ ltac:(lia) ltac:(lia) L28)|].
      split; [exact (SLK 48 _ ltac:(lia) ltac:(lia) L30)|]. split; [exact (SLK 56 _ ltac:(lia) ltac:(lia) L38)|].
      split; [exact (SLK 64 _ ltac:(lia) ltac:(lia) L40)|]. split; [exact (SLK 104 _ ltac:(lia) ltac:(lia) L68)|].
      split; [exact (SLK 112 _ ltac:(lia) ltac:(lia) L70)|]. exact (SLK 120 _ ltac:(lia) ltac:(lia) L78). }
    split; [exact (SLK 88 _ ltac:(lia) ltac:(lia) S58)|].
    split; [exact (RG 20 ltac:(unfold acallee_saved; lia) _ R20)|].
    split; [exact (RG 21 ltac:(unfold acallee_saved; lia) _ R21)|].
    split; [exact (RG 26 ltac:(unfold acallee_saved; lia) _ R26)|].
    exact (RG 27 ltac:(unfold acallee_saved; lia) _ R27).
  - split; [exact Hidx|]. split; [exact R10s|].
    split; [exact (RG 19 ltac:(unfold acallee_saved; lia) _ R19)|].
    split; [exact (RG 23 ltac:(unfold acallee_saved; lia) _ R23)|].
    exact (RG 24 ltac:(unfold acallee_saved; lia) _ R24).
Qed.

End rn.

Theorem c3_segA : forall POST, c3_segA_ok B MT POST.
Proof using HY.
  intros POST i HRN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HLE
    (pos & r & fab & op & bs & HBD & Hi & Hk & Hacc & Hblk & Hreg & Hinv & Hfab & Hprev & Hpos & Hop & Hop3 & Hcur
     & Hloop & R19 & R20 & R21 & R23 & R24 & R26 & R27).
  destruct (Nat.lt_ge_cases (S pos) (length (lc_pl cx))) as [Hlen | Hlen].
  - (* the input has a byte left: the index byte is read at the cursor *)
    remember (lx_env cx fp (ms_regs ms3) (c3A_ex cx fp r pos)) as E eqn:HEdef.
    destruct (c3A_seat B MT HY cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E HB HJ HFR HBD Hblk Hinv Hfab Hlen Hcur Hloop
                R19 R20 R21 R27 HEdef) as [HS SHOK].
    assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; apply lx_env_img).
    assert (HE : lx_E cx fp E)
      by (rewrite HEdef; apply lx_env_E; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HBD)))))))).
    assert (EFA : frame_addr ly3 LX_CID fp = lF cx fp)
      by (exact (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ)).
    assert (E23 : ew E 23 = w64 op)
      by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 23 (23%bv : bv 5)) by reflexivity;
          exact R23).
    assert (Hop64 : 0 <= op < 2 ^ 64)
      by (rewrite Hop; pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as X;
          change (bv_modulus 8) with 256 in X; lia).
    assert (UA3 : U E (SAlu ALU_AND (SOff 23 0) (SLit 3)) = 3)
      by (rewrite U_SAlu, U_SOff, U_SLit, E23; cbn [zalu_raw]; unfold w64, zcanon, M64;
          rewrite Z_to_bv_unsigned, Z.add_0_r; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          rewrite !(Z.mod_small op) by lia; change (3 mod 2 ^ 64) with 3; rewrite Hop3; reflexivity).
    pose proof HE as (EA2 & EA8 & EA3 & EA4 & EA22 & EA32 & EASV & EA46 & EA47).
    pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPceil & SP47 & SPsp1 & SPal).
    pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
    (* 0x8034c .. 0x80354: the turn number to sp1 + 0x58, then `blt s3, a0` (a0 = op & 3 = 3, s3 = 1): taken *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan;
      [ cbn [lx_ss ss_mem]; eapply lx_awr_ok;
        [ exact LAWS | exact HB | exact HJ | exact HFR | exact HE | exact EFA | lia | lia | lia | lia
        | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ] |].
    psrr_branch_tok RUN BR HS SHOK C3_Bspan;
      rewrite (denot_lit_U E (SAlu ALU_AND (SOff 23 0) (SLit 3))), UA3 in Hc; vm_compute in Hc; [|discriminate Hc].
    clear Hc.
    (* 0x803cc .. 0x803d0: `bne a0, 2`: taken, so the switch goes to case 3 at 0x804d0 *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan; [c3_awr_run EA2|].
    psrr_branch_tok RUN BR HS SHOK C3_Bspan;
      rewrite (denot_lit_U E (SAlu ALU_AND (SOff 23 0) (SLit 3))), UA3 in Hc; vm_compute in Hc; [|discriminate Hc].
    clear Hc.
    (* 0x804d0 .. 0x80824: the inlined fuzz_u8 (the UBSan wrap check and the shadow check of the cursor are decided
       by the input block's facts) and the call of read_name; the engine stops at the callee's entry. *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan; [c3_awr_run EA2|].

    (* at read_name's entry: the cut's facts from the engine's state, then the call *)
    rewrite !wvb_collapse in HJ.
    assert (EW : forall n, (n < 512)%nat -> ew (ewset (ewset E 512 w) 513 w0) n = ew E n)
      by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
    assert (HE' : lx_E cx fp (ewset (ewset E 512 w) 513 w0))
      by (apply (lx_E_agree cx fp E); [exact HE | intros n Hn; apply EW; unfold LA_EX in Hn; lia]).
    assert (ER : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr (ms_regs ms3) x)
      by (intros n x Hx; rewrite HEdef; apply lx_env_reg; exact Hx).
    assert (EX : forall j, (j < 6)%nat -> ew E (LA_EX + j) = nth j (c3A_ex cx fp r pos) (w64 0))
      by (intros j Hj; rewrite HEdef; apply lx_env_ex; unfold LA_EX; lia).
    pose proof (EX 0%nat ltac:(lia)) as E48. pose proof (EX 1%nat ltac:(lia)) as E49.
    pose proof (EX 2%nat ltac:(lia)) as E50. pose proof (EX 3%nat ltac:(lia)) as E51.
    pose proof (EX 4%nat ltac:(lia)) as E52. pose proof (EX 5%nat ltac:(lia)) as E53.
    cbn [nth c3A_ex LA_EX Nat.add] in E48, E49, E50, E51, E52, E53.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite pa_sigma_read_name in HS.
    pose proof (c3_pi_of_st _ _ AF_read_name _ HS) as HSp.
  
    pose proof HB as (_ & _ & _ & Hpn & _).
    destruct Hpn as [Hn0 | (Hnpos & Hinc)]; [unfold lc_n in Hn0; lia|].
    pose proof HJ as (HAR1 & _).
    assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
      by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hinc).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin3) as (_ & Hp4096 & Hpceil & _).
    rewrite (c3_req (lc_n cx)) in Hpceil by lia.
    assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3))
      by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hrin3) as (_ & Hr4096 & Hrceil & _).
    change (req_size LX_REG) with 288 in Hrceil.
    pose proof (lx_F_facts B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR) as (HF0' & HFc & _).
    assert (XSP : YP09.base_val E (Some LA_SP) = lsp1 cx) by exact (lx_base_sp B MT cx fp HB E HE).
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + 152) ->
      aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hn.
      rewrite (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr1 ltac:(vm_compute; reflexivity) XSP a Ha Hn).
      rewrite (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr0 ltac:(vm_compute; reflexivity) XSP a Ha Hn).
      exact (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr ltac:(vm_compute; reflexivity) XSP a Ha Hn). }
    pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINP).
    assert (HINP1 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx))).
    { intros j Hj. destruct (HINP j Hj) as [Hv Hb]. split; [|exact Hb].
      intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
      pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
      rewrite length_map in Hj.
      rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms1) _
                 (K3 (lc_p cx + Z.of_nat j) ltac:(unfold lc_n in *; lia) ltac:(unfold lc_n in *; lia))).
      exact Hv0. }
  
    assert (SL : forall off e v, In (YP09.mkChunk off (CVal 8 e))
        [YP09.mkChunk 136 (CVal 8 (SOff 48 1)); YP09.mkChunk 144 (CVal 8 (SOff 49 (-1))); YP09.mkChunk 88 (CVal 8 (SOff 24 0));
         YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 46 0)); YP09.mkChunk 24 (CVal 8 (SOff 46 0));
         YP09.mkChunk 40 (CVal 8 (SOff 20 280)); YP09.mkChunk 48 (CVal 8 (SOff 27 0)); YP09.mkChunk 56 (CVal 8 (SLit 0));
         YP09.mkChunk 64 (CVal 8 (SOff 50 0)); YP09.mkChunk 104 (CVal 8 (SOff 46 32)); YP09.mkChunk 112 (CVal 8 (SOff 51 0));
         YP09.mkChunk 120 (CVal 8 (SOff 52 0)); YP09.mkChunk 128 (CVal 8 (SOff 46 0))] ->
      sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> lslot cx W3 ms1 off v).
    { intros off e v Hin He Hv.
      eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB _ _ _ _ _ _ _ off e v HE' HSp); [reflexivity | exact Hin | | exact Hv].
      rewrite <- He. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; cbn [sv_denot]; rewrite ?EW by lia; reflexivity|]).
      destruct Hin. }
    assert (D : forall n v c v', ew E n = w64 v -> 0 <= v < 2 ^ 64 -> v' = v + c -> sv_denot E (SOff n c) = w64 v')
      by (intros n v c v' H Hv ->; exact (c3a_den_off E n v c H Hv)).
    assert (E20 : ew E 20 = w64 r) by (rewrite (ER 20%nat (20%bv : bv 5)) by reflexivity; exact R20).
    assert (E24 : ew E 24 = w64 (Z.of_nat i)) by (rewrite (ER 24%nat (24%bv : bv 5)) by reflexivity; exact R24).
    assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (rewrite (ER 26%nat (26%bv : bv 5)) by reflexivity; exact R26).
    assert (E27 : ew E 27 = w64 fab) by (rewrite (ER 27%nat (27%bv : bv 5)) by reflexivity; exact R27).
    pose proof Hloop as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
    pose proof (c3a_rdword_range _ _ _ _ L30) as Rfab.
    pose proof (c3a_rdword_range _ _ _ _ L40) as Rsh.
    pose proof (c3a_rdword_range _ _ _ _ L70) as Rnr.
    pose proof (c3a_rdword_range _ _ _ _ L78) as Rnp.
    pose proof Hcur as (_ & C88 & C90).
    pose proof (c3a_rdword_range _ _ _ _ C88) as Rp. pose proof (c3a_rdword_range _ _ _ _ C90) as Rn.
    assert (HF46 : 0 <= lF cx fp < 2 ^ 64) by lia.
    assert (S88 : lslot cx W3 ms1 136 (lc_p cx + Z.of_nat (S (S pos))))
      by (apply (SL 136 (SOff 48 1)); [c3_in | apply (D 48%nat (lc_p cx + Z.of_nat (S pos))); [exact E48 | lia | lia] | unfold lc_n in *; lia]).
    assert (S90 : lslot cx W3 ms1 144 (lc_n cx - Z.of_nat (S (S pos))))
      by (apply (SL 144 (SOff 49 (-1))); [c3_in | apply (D 49%nat (lc_n cx - Z.of_nat (S pos))); [exact E49 | lia | lia] | unfold lc_n in *; lia]).
    assert (S58 : lslot cx W3 ms1 88 (Z.of_nat i))
      by (apply (SL 88 (SOff 24 0)); [c3_in | apply (D 24%nat (Z.of_nat i)); [exact E24 | lia | lia] | lia]).
    assert (S10 : lslot cx W3 ms1 16 (lF cx fp))
      by (apply (SL 16 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (S18 : lslot cx W3 ms1 24 (lF cx fp))
      by (apply (SL 24 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (S80 : lslot cx W3 ms1 128 (lF cx fp))
      by (apply (SL 128 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (Hloop1 : lslots_loop cx fp W3 ms1 r fab).
    { split; [apply (SL 8 (SLit 3)); [c3_in | reflexivity | lia]|].
      split; [apply (SL 40 (SOff 20 280)); [c3_in | apply (D 20%nat r); [exact E20 | lia | lia] | lia]|].
      split; [apply (SL 48 (SOff 27 0)); [c3_in | apply (D 27%nat fab); [exact E27 | lia | lia] | lia]|].
      split; [apply (SL 56 (SLit 0)); [c3_in | reflexivity | lia]|].
      split; [apply (SL 64 (SOff 50 0)); [c3_in | apply (D 50%nat (shadow_addr (r + 280))); [exact E50 | lia | lia] | lia]|].
      split; [apply (SL 104 (SOff 46 32)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]|].
      split; [apply (SL 112 (SOff 51 0)); [c3_in | apply (D 51%nat (2 ^ 64 - 1 - r)); [exact E51 | lia | lia] | lia]|].
      apply (SL 120 (SOff 52 0)); [c3_in | apply (D 52%nat (2 ^ 64 - 1 - (lF cx fp + 64))); [exact E52 | lia | lia] | lia]. }
    assert (HBD1 : lx_body cx fp AF_read_name W3 ms1 LSH_iter).
    { apply (lx_land cx fp W3 ms1 _ AF_read_name _ LSH_iter HE' HSp); try reflexivity.
      - exact (lx_saved_of_ss B MT cx fp W3 ms1 HB _ _ HE' HSp eq_refl).
      - eapply (lx_shadow_of_ss B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR _ _ _ _ _ _ _ LSH_iter HE' HSp);
          [reflexivity | vm_compute; reflexivity].
      - eapply (lx_flag_of_ss B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR _ _ _ _ _ _ _ HE' HSp); [reflexivity | c3_in].
      - exact S10.
      - exact S18.
      - exact S80.
      - exact HINP1. }
    assert (Hreg1 : lreg W3 ms1 r bs)
      by (intros j Hj; unfold lview; rewrite K3 by (unfold LX_REG in Hj; lia); exact (Hreg j Hj)).
    assert (Hprev1 : lprev cx fp W3 ms1 bs)
      by (intros j Hj; unfold lview; rewrite K3 by (unfold LX_REG in Hj; lia); exact (Hprev j Hj)).
    pose proof (bv_unsigned_in_range 8 (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))) as Hby. change (bv_modulus 8) with 256 in Hby.
    pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as Hob. change (bv_modulus 8) with 256 in Hob.
    assert (HPl : (S (S pos) <= length (lc_pl cx))%nat) by lia.
    apply (c3a_call POST i HRN cx fp k acc ly3 S3 W3 ms1 _ (S (S pos)) r fab op
             (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))) bs HB HJ ltac:(unfold lc_n; lia) HFR HLE Hi Hk Hacc Hblk
             Hinv Hfab Hop3 ltac:(lia) Hby HBD1 Hreg1 Hprev1 (conj HPl (conj S88 S90)) Hloop1 S58).
    + rewrite Q1. reflexivity.
    + rewrite Q10. unfold LA_SP in EA2. rewrite EA2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + exact Q19.
    + rewrite Q20. exact E20.
    + rewrite Q21. unfold LA_F in EA46. rewrite EA46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + rewrite Q23. exact E23.
    + rewrite Q24. exact E53.
    + rewrite Q26. exact E26.
    + rewrite Q27. exact E27.
  - (* the input is used up: fuzz_u8 gives 0 (beqz 0x804d4 -> 0x8081c, mv s8, zero) *)
    assert (Hend : S pos = length (lc_pl cx)) by (pose proof Hcur as (Hcl & _); lia).
    remember (lx_env cx fp (ms_regs ms3) (c3A_ex cx fp r pos)) as E eqn:HEdef.
    pose proof (c3A0_seat cx fp k ly3 S3 W3 ms3 md3 pos r fab bs E HB HJ HFR HBD Hblk Hinv Hfab Hend Hcur Hloop
                R19 R20 R21 R27 HEdef) as HS.
    assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
    assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; apply lx_env_img).
    assert (HE : lx_E cx fp E)
      by (rewrite HEdef; apply lx_env_E; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HBD)))))))).
    assert (EFA : frame_addr ly3 LX_CID fp = lF cx fp)
      by (exact (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ)).
    assert (E23 : ew E 23 = w64 op)
      by (rewrite HEdef, (lx_env_reg cx fp (ms_regs ms3) (c3A_ex cx fp r pos) 23 (23%bv : bv 5)) by reflexivity;
          exact R23).
    assert (Hop64 : 0 <= op < 2 ^ 64)
      by (rewrite Hop; pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as X;
          change (bv_modulus 8) with 256 in X; lia).
    assert (UA3 : U E (SAlu ALU_AND (SOff 23 0) (SLit 3)) = 3)
      by (rewrite U_SAlu, U_SOff, U_SLit, E23; cbn [zalu_raw]; unfold w64, zcanon, M64;
          rewrite Z_to_bv_unsigned, Z.add_0_r; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
          rewrite !(Z.mod_small op) by lia; change (3 mod 2 ^ 64) with 3; rewrite Hop3; reflexivity).
    pose proof HE as (EA2 & EA8 & EA3 & EA4 & EA22 & EA32 & EASV & EA46 & EA47).
    pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPceil & SP47 & SPsp1 & SPal).
    pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
    (* 0x8034c .. 0x80354: the turn number to sp1 + 0x58, then `blt s3, a0` (a0 = op & 3 = 3, s3 = 1): taken *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan;
      [ cbn [lx_ss ss_mem]; eapply lx_awr_ok;
        [ exact LAWS | exact HB | exact HJ | exact HFR | exact HE | exact EFA | lia | lia | lia | lia | apply awr_ok_nil ] |].
    psrr_branch_tok RUN BR HS SHOK C3_Bspan;
      rewrite (denot_lit_U E (SAlu ALU_AND (SOff 23 0) (SLit 3))), UA3 in Hc; vm_compute in Hc; [|discriminate Hc].
    clear Hc.
    (* 0x803cc .. 0x803d0: `bne a0, 2`: taken, so the switch goes to case 3 at 0x804d0 *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan; [c3_awr_run EA2|].
    psrr_branch_tok RUN BR HS SHOK C3_Bspan;
      rewrite (denot_lit_U E (SAlu ALU_AND (SOff 23 0) (SLit 3))), UA3 in Hc; vm_compute in Hc; [|discriminate Hc].
    clear Hc.
    (* 0x804d0 .. 0x804d4: the cursor's n (atom 49, 0 here) and `beqz`: taken *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan; [c3_awr_run EA2|].
    psrr_branch_tok RUN BR HS SHOK C3_Bspan.
    2: { exfalso.
         assert (E49 : ew E 49 = w64 0)
           by (rewrite HEdef; change 49%nat with (LA_EX + 1)%nat; rewrite lx_env_ex by (unfold LA_EX; lia);
               cbn [nth c3A_ex]; f_equal; unfold lc_n; lia).
         rewrite lx_sv_SOff0, E49 in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    (* 0x8081c .. 0x80824: s8 = 0, a0 = s1 + 0x88, the call of read_name; the engine stops at the callee's entry *)
    paj_run_tok RUN HS HJ SHOK C3_Bspan; [c3_awr_run EA2|].

    (* at read_name's entry: the cut's facts from the engine's state, then the call *)
    rewrite !wvb_collapse in HJ.
    assert (ER : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr (ms_regs ms3) x)
      by (intros n x Hx; rewrite HEdef; apply lx_env_reg; exact Hx).
    assert (EX : forall j, (j < 6)%nat -> ew E (LA_EX + j) = nth j (c3A_ex cx fp r pos) (w64 0))
      by (intros j Hj; rewrite HEdef; apply lx_env_ex; unfold LA_EX; lia).
    pose proof (EX 0%nat ltac:(lia)) as E48. pose proof (EX 1%nat ltac:(lia)) as E49.
    pose proof (EX 2%nat ltac:(lia)) as E50. pose proof (EX 3%nat ltac:(lia)) as E51.
    pose proof (EX 4%nat ltac:(lia)) as E52.
    cbn [nth c3A_ex LA_EX Nat.add] in E48, E49, E50, E51, E52.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite pa_sigma_read_name in HS.
    pose proof (c3_pi_of_st _ _ AF_read_name _ HS) as HSp.
    pose proof HB as (_ & _ & _ & Hpn & _).
    destruct Hpn as [Hn0 | (Hnpos & Hinc)]; [unfold lc_n in Hn0; lia|].
    pose proof HJ as (HAR2 & _).
    assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
      by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hinc).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin3) as (_ & Hp4096 & Hpceil & _).
    rewrite (c3_req (lc_n cx)) in Hpceil by lia.
    assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3))
      by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hrin3) as (_ & Hr4096 & Hrceil & _).
    change (req_size LX_REG) with 288 in Hrceil.
    pose proof (lx_F_facts B MT LAWS cx fp W3 ms2 ly3 S3 _ k HB HJ HFR) as (HF0' & HFc & _).
    assert (XSP : YP09.base_val E (Some LA_SP) = lsp1 cx) by exact (lx_base_sp B MT cx fp HB E HE).
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + 152) ->
      aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hn.
      rewrite (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr2 ltac:(vm_compute; reflexivity) XSP a Ha Hn).
      rewrite (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr1 ltac:(vm_compute; reflexivity) XSP a Ha Hn).
      rewrite (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr0 ltac:(vm_compute; reflexivity) XSP a Ha Hn).
      exact (c3a_kept_win E _ (w_H W3) _ _ (lsp1 cx) HFr ltac:(vm_compute; reflexivity) XSP a Ha Hn). }
    pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINP).
    assert (HINP1 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms2)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx))).
    { intros j Hj. destruct (HINP j Hj) as [Hv Hb]. split; [|exact Hb].
      intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
      pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
      rewrite length_map in Hj.
      rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms2) _
                 (K3 (lc_p cx + Z.of_nat j) ltac:(unfold lc_n in *; lia) ltac:(unfold lc_n in *; lia))).
      exact Hv0. }
    assert (SL : forall off e v, In (YP09.mkChunk off (CVal 8 e))
        [YP09.mkChunk 88 (CVal 8 (SOff 24 0)); YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 46 0));
         YP09.mkChunk 24 (CVal 8 (SOff 46 0)); YP09.mkChunk 40 (CVal 8 (SOff 20 280)); YP09.mkChunk 48 (CVal 8 (SOff 27 0));
         YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 64 (CVal 8 (SOff 50 0)); YP09.mkChunk 104 (CVal 8 (SOff 46 32));
         YP09.mkChunk 112 (CVal 8 (SOff 51 0)); YP09.mkChunk 120 (CVal 8 (SOff 52 0)); YP09.mkChunk 128 (CVal 8 (SOff 46 0));
         YP09.mkChunk 136 (CVal 8 (SOff 48 0)); YP09.mkChunk 144 (CVal 8 (SOff 49 0))] ->
      sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> lslot cx W3 ms2 off v)
      by (intros off e v Hin He Hv;
          eapply (lx_slot_of_ss B MT cx fp W3 ms2 HB _ _ _ _ _ _ _ off e v HE HSp); [reflexivity | exact Hin | exact He | exact Hv]).
    assert (D : forall n v c v', ew E n = w64 v -> 0 <= v < 2 ^ 64 -> v' = v + c -> sv_denot E (SOff n c) = w64 v')
      by (intros n v c v' H Hv ->; exact (c3a_den_off E n v c H Hv)).
    assert (E20 : ew E 20 = w64 r) by (rewrite (ER 20%nat (20%bv : bv 5)) by reflexivity; exact R20).
    assert (E24 : ew E 24 = w64 (Z.of_nat i)) by (rewrite (ER 24%nat (24%bv : bv 5)) by reflexivity; exact R24).
    assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (rewrite (ER 26%nat (26%bv : bv 5)) by reflexivity; exact R26).
    assert (E27 : ew E 27 = w64 fab) by (rewrite (ER 27%nat (27%bv : bv 5)) by reflexivity; exact R27).
    pose proof Hloop as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
    pose proof (c3a_rdword_range _ _ _ _ L30) as Rfab.
    pose proof (c3a_rdword_range _ _ _ _ L40) as Rsh.
    pose proof (c3a_rdword_range _ _ _ _ L70) as Rnr.
    pose proof (c3a_rdword_range _ _ _ _ L78) as Rnp.
    assert (HF46 : 0 <= lF cx fp < 2 ^ 64) by lia.
    assert (S88 : lslot cx W3 ms2 136 (lc_p cx + Z.of_nat (S pos)))
      by (apply (SL 136 (SOff 48 0)); [c3_in | apply (D 48%nat (lc_p cx + Z.of_nat (S pos))); [exact E48 | unfold lc_n in *; lia | lia] | unfold lc_n in *; lia]).
    assert (S90 : lslot cx W3 ms2 144 (lc_n cx - Z.of_nat (S pos)))
      by (apply (SL 144 (SOff 49 0)); [c3_in | apply (D 49%nat (lc_n cx - Z.of_nat (S pos))); [exact E49 | unfold lc_n in *; lia | lia] | unfold lc_n in *; lia]).
    assert (S58 : lslot cx W3 ms2 88 (Z.of_nat i))
      by (apply (SL 88 (SOff 24 0)); [c3_in | apply (D 24%nat (Z.of_nat i)); [exact E24 | lia | lia] | lia]).
    assert (S10 : lslot cx W3 ms2 16 (lF cx fp))
      by (apply (SL 16 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (S18 : lslot cx W3 ms2 24 (lF cx fp))
      by (apply (SL 24 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (S80 : lslot cx W3 ms2 128 (lF cx fp))
      by (apply (SL 128 (SOff 46 0)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]).
    assert (Hloop1 : lslots_loop cx fp W3 ms2 r fab).
    { split; [apply (SL 8 (SLit 3)); [c3_in | reflexivity | lia]|].
      split; [apply (SL 40 (SOff 20 280)); [c3_in | apply (D 20%nat r); [exact E20 | lia | lia] | lia]|].
      split; [apply (SL 48 (SOff 27 0)); [c3_in | apply (D 27%nat fab); [exact E27 | lia | lia] | lia]|].
      split; [apply (SL 56 (SLit 0)); [c3_in | reflexivity | lia]|].
      split; [apply (SL 64 (SOff 50 0)); [c3_in | apply (D 50%nat (shadow_addr (r + 280))); [exact E50 | lia | lia] | lia]|].
      split; [apply (SL 104 (SOff 46 32)); [c3_in | apply (D 46%nat (lF cx fp)); [exact EA46 | lia | lia] | lia]|].
      split; [apply (SL 112 (SOff 51 0)); [c3_in | apply (D 51%nat (2 ^ 64 - 1 - r)); [exact E51 | lia | lia] | lia]|].
      apply (SL 120 (SOff 52 0)); [c3_in | apply (D 52%nat (2 ^ 64 - 1 - (lF cx fp + 64))); [exact E52 | lia | lia] | lia]. }
    assert (HBD1 : lx_body cx fp AF_read_name W3 ms2 LSH_iter).
    { apply (lx_land cx fp W3 ms2 _ AF_read_name _ LSH_iter HE HSp); try reflexivity.
      - exact (lx_saved_of_ss B MT cx fp W3 ms2 HB _ _ HE HSp eq_refl).
      - eapply (lx_shadow_of_ss B MT LAWS cx fp W3 ms2 ly3 S3 _ k HB HJ HFR _ _ _ _ _ _ _ LSH_iter HE HSp);
          [reflexivity | vm_compute; reflexivity].
      - eapply (lx_flag_of_ss B MT LAWS cx fp W3 ms2 ly3 S3 _ k HB HJ HFR _ _ _ _ _ _ _ HE HSp); [reflexivity | c3_in].
      - exact S10.
      - exact S18.
      - exact S80.
      - exact HINP1. }
    assert (Hreg1 : lreg W3 ms2 r bs)
      by (intros j Hj; unfold lview; rewrite K3 by (unfold LX_REG in Hj; lia); exact (Hreg j Hj)).
    assert (Hprev1 : lprev cx fp W3 ms2 bs)
      by (intros j Hj; unfold lview; rewrite K3 by (unfold LX_REG in Hj; lia); exact (Hprev j Hj)).
    pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as Hob. change (bv_modulus 8) with 256 in Hob.
    assert (HPl : (S pos <= length (lc_pl cx))%nat) by lia.
    apply (c3a_call POST i HRN cx fp k acc ly3 S3 W3 ms2 _ (S pos) r fab op 0 bs HB HJ ltac:(unfold lc_n; lia) HFR HLE
             Hi Hk Hacc Hblk Hinv Hfab Hop3 ltac:(lia) ltac:(lia) HBD1 Hreg1 Hprev1 (conj HPl (conj S88 S90)) Hloop1 S58).
    + rewrite Q1. reflexivity.
    + rewrite Q10. unfold LA_SP in EA2. rewrite EA2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + exact Q19.
    + rewrite Q20. exact E20.
    + rewrite Q21. unfold LA_F in EA46. rewrite EA46. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + rewrite Q23. exact E23.
    + exact Q24.
    + rewrite Q26. exact E26.
    + rewrite Q27. exact E27.
Qed.

End a.
