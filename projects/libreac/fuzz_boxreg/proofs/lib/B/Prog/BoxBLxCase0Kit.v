(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 662 of its 760 lines of code are new or changed and 833 lines of the source are left out. *)
(* The tools the middle pieces of case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput share
   (BoxBLxCase0N.v, BoxBLxCase0RF.v, BoxBLxCase0L.v, BoxBLxCase0W.v; the cuts are BoxBLxCase0Defs.v's).
   No instruction of these pieces checks a shadow byte or traps, so each piece seats the machine state with the
   registers as atoms 0 .. 31 and only the spill slots it reads or writes as regions (the form of
   BoxBLxCase1Want.v's cw_seat), and carries every other byte a cut speaks about by `c0_kept`: the bytes at or above
   the realigned stack pointer but the slots the piece writes (0x20 = want, 0x60 = the name), the caller's input,
   the frame and its shadow, and the heap blocks the piece holds (the registry r and the name). *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBRangeFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c range_free_c
  lowest_free_c reac_boxreg_declare_c LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The engine's shadow base: no shadow check runs in these pieces. *)
Definition C0K_SB : Z := 0x7fff8000.
Definition C0K_BX : sv := SLit C0K_SB.
Definition C0K_BSPAN : Z * Z := (C0K_SB, C0K_SB + 2 ^ 44 - 1).
(* sp = s1 = sp1 is above the shadow span, which sh_static_ok asks of a write window's base atom. *)
Definition C0K_SPF : facts := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5)] [] [].
Definition c0k_ss (pc : Z) (rs : YP09.smem) (G : facts) : sstate := mkSS pc sr_atoms rs None G.
(* A spill-slot region over [lo, hi) of sp1 (atom 9), with the write window [wlo, whi). *)
Definition c0k_reg (lo hi wlo whi : Z) (l : list (Z * sv)) : YP09.region :=
  YP09.mkRegion (Some 9%nat) lo hi wlo whi (lx_slot_chunks l).

(* ---- the branches, decided on the words their operands denote ---- *)
Lemma c0k_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma c0k_denot_lit : forall E z, sv_denot E (SLit z) = w64 z.
Proof. intros E z. reflexivity. Qed.

Lemma c0k_atom0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv.
  rewrite Z.add_0_r. reflexivity.
Qed.

Lemma c0k_br_lt : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. cbn [branch_taken]. rewrite Ha, Hb. apply Boxreg.lts_lit; lia. Qed.

Lemma c0k_br_ltu : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_ltu_U. unfold U. rewrite Ha, Hb. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma c0k_br_eq : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_eq_U. unfold U. rewrite Ha, Hb. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma c0k_br_ne : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_ne_U. unfold U. rewrite Ha, Hb. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma c0k_denot_a0 : forall E k (regs2 : bvmap 5 word),
  sv_denot (havoc E k (map (getr regs2) CLOB)) (SOff (k + 4) 0) = getr regs2 10.
Proof.
  intros E k regs2. cbn [sv_denot]. unfold havoc. cbn [ew].
  replace (k + 4 <? k)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + 4 - k)%nat with 4%nat by lia.
  cbn [map CLOB nth]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c0k_addw : forall E a c x y, sv_denot E a = w64 x -> sv_denot E c = w64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 31 -> sv_denot E (SAluw ALU_ADD a c) = w64 (x + y).
Proof.
  intros E a c x y Ha Hc Hx Hy Hxy. cbn [sv_denot]. rewrite Ha, Hc. unfold w64.
  rewrite (aluw_addsub_of_lit ALU_ADD _ _ (x + y) (or_introl eq_refl) (alu64_add_lit x y)).
  f_equal. unfold zalu32, zcanon, zu32, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [zalu_raw].
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  unfold M32. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma c0k_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->]. apply Z.mod_divide; [lia|]. exists (2 * x). lia.
Qed.

(* ---- the tactics of the pieces ---- *)
(* A register of a symbolic state as the term the state holds (no normalization). *)
Ltac c0k_rawreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* After a run over read-only regions: the memory is the one before. *)
Ltac c0k_ro HM :=
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* The slot 0x20 after range_free returned (0x8056c snez, 0x80570 addiw -1, 0x80574 or s10): the mask trick gives
   base when a0 <> 0 and -1 when a0 = 0 (LLVMFuzzerTestOneInput_case0.v c0_rf_one / c0_rf_zero). *)
Lemma c0k_lor_ones : forall b, 0 <= b < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) b = 2 ^ 64 - 1.
Proof.
  intros b Hb. change (2 ^ 64 - 1) with (Z.ones 64). apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec. destruct (Z.lt_ge_cases n 64).
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small b (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma c0k_U_rf : forall E na nb a b, ew E na = w64 a -> ew E nb = w64 b -> (a = 0 \/ a = 1) -> 0 <= b < 2 ^ 64 ->
  U E (SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff na 0)) (SLit (-1))) (SOff nb 0)) =
  (if a =? 0 then 2 ^ 64 - 1 else b).
Proof.
  intros E na nb a b Hea Heb Ha Hb.
  rewrite !U_SAlu, !U_SLit, (U_atom E na a Hea ltac:(lia)), (U_atom E nb b Heb Hb).
  cbn [zalu_raw]. destruct Ha as [-> | ->]; cbn [Z.ltb Z.compare Z.eqb].
  - change (zcanon 0) with 0. rewrite Z.add_0_l.
    replace (zcanon (zcanon (-1))) with (2 ^ 64 - 1) by reflexivity.
    rewrite c0k_lor_ones by lia. reflexivity.
  - change (zcanon 0) with 0. replace (zcanon (zcanon 1 + zcanon (-1))) with 0 by reflexivity.
    rewrite Z.lor_0_l. apply zcanon_id. unfold M64. exact Hb.
Qed.

Lemma c0k_denot_rf : forall E na nb a b, ew E na = w64 a -> ew E nb = w64 b -> (a = 0 \/ a = 1) -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff na 0)) (SLit (-1))) (SOff nb 0)) =
  w64 (if a =? 0 then 2 ^ 64 - 1 else b).
Proof.
  intros E na nb a b Hea Heb Ha Hb. rewrite denot_lit_U, (c0k_U_rf E na nb a b Hea Heb Ha Hb). reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Lemma c0k_achain_ly : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch Ht H. unfold achain in *. rewrite Ht. exact H. Qed.
Lemma c0k_layout_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. intros n ly ly' Hle. pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _). exact Htop. Qed.

(* A seat over the registers as atoms and a few regions of the piece's choice. *)
Lemma c0k_seat : forall cx fp (W3 : world SEGS) (ms3 : machine_state) pc ex rs G,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (lx_env cx fp (ms_regs ms3) ex) (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  YP09.pairwise_disjoint (lx_env cx fp (ms_regs ms3) ex) rs ->
  facts_ok (lx_env cx fp (ms_regs ms3) ex) G ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) ex) (c0k_ss pc rs G) (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 pc ex rs G Hpc Hresv Hpend Hrom Hfregs Hfcsr Hwf Hok Hd HG.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold c0k_ss.
  apply pa_entry_st_ok_full; [apply lx_regs_ok_atoms | exact Hwf | exact Hok | exact Hd | exact HG].
Qed.

(* The facts of C0K_SPF at a seat. *)
Lemma c0k_spf_ok : forall E sp1, bv_unsigned (ew E 9) = sp1 -> 0x7fff7f800000 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  facts_ok E C0K_SPF.
Proof.
  intros E sp1 H9 Hr Ha. split; [|split; exact I]. cbn [C0K_SPF f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 5) with 32. lia.
Qed.

(* ---- the memory the cuts speak about, and what keeps it ---- *)
(* Every byte a cut of the case reads: at or above sp1 but the slots xs (8 bytes each), the caller's input, the
   frame and its shadow, and the heap blocks rs. *)
Definition c0_kat (cx : lxcx) (fp : Z) (xs : list Z) (rs : list (Z * Z)) (a : Z) : Prop :=
  (lsp1 cx <= a < 2 ^ 64 /\ Forall (fun x => ~ (lsp1 cx + x <= a < lsp1 cx + x + 8)) xs) \/
  lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/
  lSH cx fp <= a < lSH cx fp + 64 \/ Exists (fun q => fst q <= a < fst q + snd q) rs.
Definition c0_kept (cx : lxcx) (fp : Z) (W3 : world SEGS) (xs : list Z) (rs : list (Z * Z))
  (m m' : word -> option byte) : Prop :=
  forall a, c0_kat cx fp xs rs a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma c0_kept_refl : forall cx fp W3 xs rs m, c0_kept cx fp W3 xs rs m m.
Proof. intros cx fp W3 xs rs m a _. reflexivity. Qed.

Lemma c0_kept_trans : forall cx fp W3 xs rs m1 m2 m3,
  c0_kept cx fp W3 xs rs m1 m2 -> c0_kept cx fp W3 xs rs m2 m3 -> c0_kept cx fp W3 xs rs m1 m3.
Proof. intros cx fp W3 xs rs m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma c0_kept_lx : forall cx fp W3 xs rs m m', lx_keep cx fp W3 rs m m' -> c0_kept cx fp W3 xs rs m m'.
Proof.
  intros cx fp W3 xs rs m m' Hk a Ha. apply Hk. unfold lx_keep_at.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  rewrite Hfb8, Hfb.
  destruct Ha as [[H1 _] | [H | [H | [H | H]]]]; [left; exact H1 | right; left; exact H | right; right; left; exact H
    | right; right; right; left; exact H | right; right; right; right; exact H].
Qed.

(* Where the bytes of a cut lie: below sp1 but the stack part. *)
Definition c0_geo (cx : lxcx) (fp : Z) (rs : list (Z * Z)) : Prop :=
  0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47 /\
  4096 <= lF cx fp /\ lF cx fp + 512 <= lsp1 cx /\
  0 <= lSH cx fp /\ lSH cx fp + 64 <= lsp1 cx /\
  Forall (fun q => 0 <= fst q /\ fst q + snd q <= lsp1 cx) rs /\
  (lc_n cx = 0 \/ (0 <= lc_p cx /\ lc_p cx + lc_n cx <= lsp1 cx)).

Lemma c0_kept_frame : forall cx fp W3 xs rs E srs m m', c0_geo cx fp rs -> Forall (fun x => 0 <= x) xs ->
  frame_of E srs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows srs) -> YP09.base_val E b + wlo <= a < YP09.base_val E b + whi ->
     Exists (fun x => lsp1 cx + x <= a < lsp1 cx + x + 8) xs) ->
  c0_kept cx fp W3 xs rs m m'.
Proof.
  intros cx fp W3 xs rs E srs m m' (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7) HX HF Hw a Ha.
  apply (kept_of_frame E srs (w_H W3) m m' (fun a => Exists (fun x => lsp1 cx + x <= a < lsp1 cx + x + 8) xs) HF Hw a).
  - destruct Ha as [[H1 _] | [H | [H | [H | H]]]]; [lia | | lia | lia |].
    + destruct G7 as [G7 | G7]; [unfold lc_n in *; lia | lia].
    + apply Exists_exists in H as (q & Hq & Hb). rewrite Forall_forall in G6. pose proof (G6 q Hq). lia.
  - intros HXa. apply Exists_exists in HXa as (x & Hx & Hxa). rewrite Forall_forall in HX. pose proof (HX x Hx) as Hx0.
    destruct Ha as [[H1 H2] | [H | [H | [H | H]]]].
    + rewrite Forall_forall in H2. exact (H2 x Hx Hxa).
    + destruct G7 as [G7 | G7]; [unfold lc_n in *; lia | lia].
    + lia.
    + lia.
    + apply Exists_exists in H as (q & Hq & Hb). rewrite Forall_forall in G6. pose proof (G6 q Hq). lia.
Qed.


Lemma c0k_rdword_keep : forall (rd rd' : reader) a v,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

Section k.
Variables (cx : lxcx) (fp : Z) (W3 : world SEGS) (xs : list Z) (rs : list (Z * Z)) (ms ms' : machine_state).
Hypothesis K : c0_kept cx fp W3 xs rs (ms_mem ms) (ms_mem ms').
Hypothesis HX : Forall (fun x => x = 0x20 \/ x = 0x60) xs.
Hypothesis Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47.

Lemma c0_stk_kat : forall a, lsp1 cx <= a < 2 ^ 64 -> ~ (lsp1 cx + 0x20 <= a < lsp1 cx + 0x28) ->
  ~ (lsp1 cx + 0x60 <= a < lsp1 cx + 0x68) -> c0_kat cx fp xs rs a.
Proof.
  intros a H0 H1 H2. left. split; [exact H0|]. eapply Forall_impl; [|exact HX]. intros x [-> | ->]; lia.
Qed.

Lemma c0_slot_keep : forall off v, 0 <= off -> off + 8 <= 0x98 ->
  Forall (fun x => off + 8 <= x \/ x + 8 <= off) xs -> lslot cx W3 ms off v -> lslot cx W3 ms' off v.
Proof.
  intros off v H0 H1 HO Hv. unfold lslot, lview in *. eapply (c0k_rdword_keep _ _ _ v); [|exact Hv].
  intros j Hj. apply K. left. split; [lia|]. eapply Forall_impl; [|exact HO]. intros x Hx. cbv beta in Hx. lia.
Qed.

Lemma c0_xs_off : forall off, (off + 8 <= 0x20 \/ 0x28 <= off) -> (off + 8 <= 0x60 \/ 0x68 <= off) ->
  Forall (fun x => off + 8 <= x \/ x + 8 <= off) xs.
Proof. intros off H1 H2. eapply Forall_impl; [|exact HX]. intros x [-> | ->]; lia. Qed.

Lemma c0_saved_keep : lsaved cx W3 ms -> lsaved cx W3 ms'.
Proof.
  intros (Hra & Hsj). unfold lsaved, lview in *. split.
  - eapply (c0k_rdword_keep _ _ _ _); [|exact Hra]. intros j Hj. apply K. apply c0_stk_kat; lia.
  - intros j Hj. eapply (c0k_rdword_keep _ _ _ _); [|exact (Hsj j Hj)]. intros q Hq. apply K. apply c0_stk_kat; lia.
Qed.

Lemma c0_shadow_keep : lshadow cx fp W3 ms LSH_iter -> lshadow cx fp W3 ms' LSH_iter.
Proof.
  intros Hs j Hj. unfold lview in *. rewrite K; [exact (Hs j Hj)|].
  assert (Hl : length LSH_iter = 52%nat) by reflexivity. rewrite Hl in Hj.
  right; right; right; left. lia.
Qed.

Lemma c0_flag_keep :
  rdword (lview W3 ms) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) ->
  rdword (lview W3 ms') (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp).
Proof.
  intros Hv. assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity). rewrite Hfb in *.
  unfold lview in *. eapply (c0k_rdword_keep _ _ _ _); [|exact Hv]. intros j Hj. apply K. right; right; left. lia.
Qed.

Lemma c0_input_keep :
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).
Proof.
  intros Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite length_map in Hj.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') (lc_p cx + Z.of_nat j)).
  - exact Hv0.
  - apply K. right; left. unfold lc_n. lia.
Qed.

Lemma c0_blk_keep : forall q n j, In (q, n) rs -> 0 <= j < n -> lview W3 ms' (q + j) = lview W3 ms (q + j).
Proof.
  intros q n j Hin Hj. unfold lview. apply K. right; right; right; right.
  apply Exists_exists. exists (q, n). split; [exact Hin|]. cbn [fst snd]. lia.
Qed.

Lemma c0_reg_keep : forall r bs, In (r, LX_REG) rs -> lreg W3 ms r bs -> lreg W3 ms' r bs.
Proof.
  intros r bs Hin Hr q Hq. rewrite (c0_blk_keep r LX_REG q Hin Hq). exact (Hr q Hq).
Qed.

Lemma c0_prev_keep : forall bs, lprev cx fp W3 ms bs -> lprev cx fp W3 ms' bs.
Proof.
  intros bs Hp q Hq. unfold lprev, lview in *. rewrite K; [exact (Hp q Hq)|].
  right; right; left. unfold LX_REG in Hq. lia.
Qed.

Lemma c0_cur_keep : forall q, lcur cx W3 ms q -> lcur cx W3 ms' q.
Proof.
  intros q (Hq & H88 & H90). split; [exact Hq|].
  split; [apply (c0_slot_keep 0x88); [lia | lia | apply c0_xs_off; lia | exact H88]|].
  apply (c0_slot_keep 0x90); [lia | lia | apply c0_xs_off; lia | exact H90].
Qed.

Lemma c0_loop_keep : forall r fab, lslots_loop cx fp W3 ms r fab -> lslots_loop cx fp W3 ms' r fab.
Proof.
  intros r fab (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  split; [apply (c0_slot_keep 0x08); [lia | lia | apply c0_xs_off; lia | exact S08]|].
  split; [apply (c0_slot_keep 0x28); [lia | lia | apply c0_xs_off; lia | exact S28]|].
  split; [apply (c0_slot_keep 0x30); [lia | lia | apply c0_xs_off; lia | exact S30]|].
  split; [apply (c0_slot_keep 0x38); [lia | lia | apply c0_xs_off; lia | exact S38]|].
  split; [apply (c0_slot_keep 0x40); [lia | lia | apply c0_xs_off; lia | exact S40]|].
  split; [apply (c0_slot_keep 0x68); [lia | lia | apply c0_xs_off; lia | exact S68]|].
  split; [apply (c0_slot_keep 0x70); [lia | lia | apply c0_xs_off; lia | exact S70]|].
  apply (c0_slot_keep 0x78); [lia | lia | apply c0_xs_off; lia | exact S78].
Qed.

Lemma c0_args_keep : forall pos op (regs' : bvmap 5 word), getr (ms_regs ms') = getr regs' ->
  c0_args cx W3 ms pos op ->
  getr regs' 23 = w64 op -> getr regs' 25 = w64 (c0_nchv (lc_pl cx) pos) ->
  getr regs' 26 = w64 (c0_basev (lc_pl cx) pos) -> c0_args cx W3 ms' pos op.
Proof.
  intros pos op regs' Hr (_ & _ & _ & S50) G23 G25 G26. unfold c0_args. rewrite Hr.
  split; [exact G23|]. split; [exact G25|]. split; [exact G26|].
  apply (c0_slot_keep 0x50); [lia | lia | apply c0_xs_off; lia | exact S50].
Qed.

End k.

Lemma c0_slot_keepX : forall cx fp W3 xs rs (ms ms' : machine_state),
  c0_kept cx fp W3 xs rs (ms_mem ms) (ms_mem ms') -> Forall (fun x => x = 0x20 \/ x = 0x60) xs ->
  0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47 ->
  forall off v, 0 <= off -> off + 8 <= 0x98 -> (off + 8 <= 0x20 \/ 0x28 <= off) -> (off + 8 <= 0x60 \/ 0x68 <= off) ->
  lslot cx W3 ms off v -> lslot cx W3 ms' off v.
Proof.
  intros cx fp W3 xs rs ms ms' K HX Hsp off v H0 H1 H2 H3 Hv.
  exact (c0_slot_keep cx fp W3 xs rs ms ms' K Hsp off v H0 H1 (c0_xs_off xs HX off H2 H3) Hv).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The geometry of a cut's bytes, from the journal and the blocks. *)
Lemma c0_geo_of : forall cx fp W3 (ms3 : machine_state) ly3 S3 md3 k rs,
  lx_base B MT cx -> AR_laws SEGS B ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun q => exists n, In (fst q, n) (ablocks B ly3 S3) /\ 0 <= snd q <= req_size n) rs ->
  c0_geo cx fp rs.
Proof.
  intros cx fp W3 ms3 ly3 S3 md3 k rs HB LAWS HJ HFR Hbl Hrs.
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HFal & HSHeq).
  pose proof asan_consts as (C1a & _).
  pose proof HJ as (HAR3 & _).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite HSHeq; unfold SHADOW_OFF; lia|]. split; [rewrite HSHeq; unfold SHADOW_OFF; lia|].
  split.
  { eapply Forall_impl; [|exact Hrs]. intros [q n0] (n & Hin & Hn). cbn [fst snd] in *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR3 Hin) as (_ & Hq4096 & Hqceil & _ & _ & _). lia. }
  destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [Hn0 | (Hn & Hin)]; [left; exact (proj1 Hn0) | right].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (Hbl _ _ Hin)) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.

(* The common facts of a cut at the state (regs', pc', m') from those at ms and the bytes kept since. *)
Lemma c0_land : forall i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte)
  (regs' : bvmap 5 word) pc0 pc' pos r fab op nm bs xs rs,
  lx_base B MT cx ->
  c0_com i cx fp W3 ms pc0 pos r fab op bs -> c0_nm B MT i cx k acc ly3 S3 W3 ms pos r nm ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' ->
  getr regs' 2 = w64 (lsp1 cx) -> getr regs' 8 = w64 (lsp0 cx) -> getr regs' 9 = w64 (lsp1 cx) ->
  getr regs' 3 = getr (lc_regs cx) 3 -> getr regs' 4 = getr (lc_regs cx) 4 ->
  getr regs' 18 = w64 SHADOW_OFF -> getr regs' 22 = w64 (lSH cx fp) ->
  getr regs' 20 = w64 r -> getr regs' 21 = w64 (lF cx fp + 64) -> getr regs' 27 = w64 fab ->
  c0_com i cx fp W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) pc' pos r fab op bs /\
  c0_nm B MT i cx k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) pos r nm.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms m' regs' pc0 pc' pos r fab op nm bs xs rs HB HCOM HNM HX Hnm HK
    G2 G8 G9 G3 G4 G18 G22 G20 G21 G27.
  set (ms' := mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & Hsp0hi & Hsp1 & _).
  pose proof asan_consts as (C1a & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  assert (K : c0_kept cx fp W3 xs rs (ms_mem ms) (ms_mem ms')) by exact HK.
  destruct HCOM as (HBD & Hi & HPREV & HINV & HFAB & Hpos & Hop & Hop3 & HSLL & S58 & S48 & R20 & R21 & R27).
  destruct HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct HNM as (Hk & Hacc & Hbl & Haf & Hnm4 & Hname & Hcur).
  split.
  - split; [|split; [exact Hi|]].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
      split; [exact (c0_saved_keep cx fp W3 xs rs ms ms' K HX Hsp HSAVED)|].
      split; [exact (c0_shadow_keep cx fp W3 xs rs ms ms' K HSHD)|].
      split; [exact (c0_flag_keep cx fp W3 xs rs ms ms' K HFLAG)|].
      split; [exact (c0_slot_keepX cx fp W3 xs rs ms ms' K HX Hsp 0x10 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HS10)|].
      split; [exact (c0_slot_keepX cx fp W3 xs rs ms ms' K HX Hsp 0x18 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HS18)|].
      split; [exact (c0_slot_keepX cx fp W3 xs rs ms ms' K HX Hsp 0x80 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HS80)|].
      exact (c0_input_keep cx fp W3 xs rs ms ms' K HINP).
    + split; [exact (c0_prev_keep cx fp W3 xs rs ms ms' K bs HPREV)|].
      split; [exact HINV|]. split; [exact HFAB|]. split; [exact Hpos|]. split; [exact Hop|]. split; [exact Hop3|].
      split; [exact (c0_loop_keep cx fp W3 xs rs ms ms' K HX Hsp r fab HSLL)|].
      split; [exact (c0_slot_keepX cx fp W3 xs rs ms ms' K HX Hsp 0x58 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S58)|].
      split; [exact (c0_slot_keepX cx fp W3 xs rs ms ms' K HX Hsp 0x48 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S48)|].
      split; [exact G20|]. split; [exact G21 | exact G27].
  - split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Haf|]. split; [exact Hnm4|].
    split; [|exact (c0_cur_keep cx fp W3 xs rs ms ms' K HX Hsp _ Hcur)].
    intros j Hj. rewrite (c0_blk_keep cx fp W3 xs rs ms ms' K _ _ j Hnm ltac:(lia)). exact (Hname j Hj).
Qed.


(* The common premises of the landings below: the cut's facts at ms, the bytes kept since, the journal at m'. *)
Definition c0_from (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (pc0 : Z) (pos : nat) (r fab op nm : Z) (bs : list byte) : Prop :=
  c0_com i cx fp W3 ms pc0 pos r fab op bs /\ c0_nm B MT i cx k acc ly3 S3 W3 ms pos r nm /\
  c0_args cx W3 ms pos op.

(* The registers every landing sets from the seat's atoms. *)
Definition c0_regs (cx : lxcx) (fp : Z) (regs' : bvmap 5 word) (r fab op : Z) (pos : nat) : Prop :=
  getr regs' 2 = w64 (lsp1 cx) /\ getr regs' 8 = w64 (lsp0 cx) /\ getr regs' 9 = w64 (lsp1 cx) /\
  getr regs' 3 = getr (lc_regs cx) 3 /\ getr regs' 4 = getr (lc_regs cx) 4 /\
  getr regs' 18 = w64 SHADOW_OFF /\ getr regs' 22 = w64 (lSH cx fp) /\
  getr regs' 20 = w64 r /\ getr regs' 21 = w64 (lF cx fp + 64) /\ getr regs' 27 = w64 fab /\
  getr regs' 23 = w64 op /\ getr regs' 25 = w64 (c0_nchv (lc_pl cx) pos) /\
  getr regs' 26 = w64 (c0_basev (lc_pl cx) pos).

Lemma c0_land_all : forall i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte)
  (regs' : bvmap 5 word) pc0 pc' pos r fab op nm bs xs rs,
  lx_base B MT cx -> c0_from i cx fp k acc ly3 S3 W3 ms pc0 pos r fab op nm bs ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' -> c0_regs cx fp regs' r fab op pos ->
  c0_com i cx fp W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) pc' pos r fab op bs /\
  c0_nm B MT i cx k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) pos r nm /\
  c0_args cx W3 (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) pos op.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms m' regs' pc0 pc' pos r fab op nm bs xs rs HB (HCOM & HNM & HARG) HX Hnm HK
    (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27 & G23 & G25 & G26).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & Hsp0hi & Hsp1 & _).
  pose proof asan_consts as (C1a & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  destruct (c0_land i cx fp k acc ly3 S3 W3 ms m' regs' pc0 pc' pos r fab op nm bs xs rs HB HCOM HNM HX Hnm HK
    G2 G8 G9 G3 G4 G18 G22 G20 G21 G27) as [HC HN].
  split; [exact HC|]. split; [exact HN|].
  exact (c0_args_keep cx fp W3 xs rs ms (mkst regs' (Z_to_bv 64 (BASE + pc')) m' (seg_rom SEGS)) HK HX Hsp
    pos op regs' eq_refl HARG G23 G25 G26).
Qed.

(* ---- the landings at the cuts ---- *)
Lemma c0_to_w : forall POST i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte) md'
  (regs' : bvmap 5 word) pc0 pos r fab op nm bs want xs rs,
  lx_from B MT POST (C0_W B MT i) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m' md' k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c0_from i cx fp k acc ly3 S3 W3 ms pc0 pos r fab op nm bs -> lreg W3 ms r bs ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (r, LX_REG) rs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x20) = Some (want mod 2 ^ 64) ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x60) = Some nm ->
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want ->
  -1 <= want <= 40 ->
  c0_regs cx fp regs' r fab op pos -> getr regs' 19 = w64 nm ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C0P_W)) m' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros POST i cx fp k acc ly3 S3 W3 ms m' md' regs' pc0 pos r fab op nm bs want xs rs
    HN HB HJ HFR HMO HF HREG HX Hr Hnm HK S20 S60 HW Hw HR G19.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + C0P_W)) m' (seg_rom SEGS)) md' HB HJ HFR HMO).
  destruct (c0_land_all i cx fp k acc ly3 S3 W3 ms m' regs' pc0 C0P_W pos r fab op nm bs xs rs HB HF HX Hnm HK HR)
    as (HC & HNM & HARG).
  exists pos, r, fab, op, nm, want, bs.
  split; [exact HC|]. split; [exact HNM|].
  split; [exact (c0_reg_keep cx fp W3 xs rs ms (mkst regs' (Z_to_bv 64 (BASE + C0P_W)) m' (seg_rom SEGS)) HK r bs Hr HREG)|].
  split; [exact HARG|]. split; [exact G19|]. split; [exact S60|]. split; [exact HW|]. split; [exact Hw | exact S20].
Qed.

Lemma c0_to_rf : forall POST i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte) md'
  (regs' : bvmap 5 word) pc0 pos r fab op nm bs xs rs,
  lx_from B MT POST (C0_RF B MT i) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m' md' k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c0_from i cx fp k acc ly3 S3 W3 ms pc0 pos r fab op nm bs -> lreg W3 ms r bs ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (r, LX_REG) rs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x60) = Some nm ->
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab -> Boxreg.bx_n bs < 5 ->
  0 <= c0_basev (lc_pl cx) pos ->
  ((range_free_c.range_free_ok bs (c0_basev (lc_pl cx) pos) (c0_nchv (lc_pl cx) pos) fab /\ getr regs' 10 = w64 1) \/
   (~ range_free_c.range_free_ok bs (c0_basev (lc_pl cx) pos) (c0_nchv (lc_pl cx) pos) fab /\ getr regs' 10 = w64 0)) ->
  c0_regs cx fp regs' r fab op pos -> getr regs' 19 = w64 nm ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C0P_RF)) m' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros POST i cx fp k acc ly3 S3 W3 ms m' md' regs' pc0 pos r fab op nm bs xs rs
    HN HB HJ HFR HMO HF HREG HX Hr Hnm HK S60 Hok Hn5 Hb0 HRES HR G19.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + C0P_RF)) m' (seg_rom SEGS)) md' HB HJ HFR HMO).
  destruct (c0_land_all i cx fp k acc ly3 S3 W3 ms m' regs' pc0 C0P_RF pos r fab op nm bs xs rs HB HF HX Hnm HK HR)
    as (HC & HNM & HARG).
  exists pos, r, fab, op, nm, bs.
  split; [exact HC|]. split; [exact HNM|].
  split; [exact (c0_reg_keep cx fp W3 xs rs ms (mkst regs' (Z_to_bv 64 (BASE + C0P_RF)) m' (seg_rom SEGS)) HK r bs Hr HREG)|].
  split; [exact HARG|]. split; [exact G19|]. split; [exact S60|]. split; [exact Hok|]. split; [exact Hn5|].
  split; [exact Hb0 | exact HRES].
Qed.

Lemma c0_to_l : forall POST i j cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte) md'
  (regs' : bvmap 5 word) pc0 pos r fab op nm bs xs rs,
  lx_from B MT POST (C0_L B MT i j) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m' md' k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c0_from i cx fp k acc ly3 S3 W3 ms pc0 pos r fab op nm bs -> lreg W3 ms r bs ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (r, LX_REG) rs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x20) = Some (2 ^ 64 - 1) ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x60) = Some nm ->
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab -> Boxreg.bx_n bs < 5 ->
  c0_basev (lc_pl cx) pos < 0 -> 0 <= j <= fab - c0_nchv (lc_pl cx) pos ->
  (forall b, 0 <= b < j -> ~ range_free_c.range_free_ok bs b (c0_nchv (lc_pl cx) pos) fab) ->
  c0_regs cx fp regs' r fab op pos -> getr regs' 19 = w64 j ->
  getr regs' 24 = w64 (fab - c0_nchv (lc_pl cx) pos + 1) ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C0P_L)) m' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros POST i j cx fp k acc ly3 S3 W3 ms m' md' regs' pc0 pos r fab op nm bs xs rs
    HN HB HJ HFR HMO HF HREG HX Hr Hnm HK S20 S60 Hok Hn5 Hb0 Hj Hlf HR G19 G24.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + C0P_L)) m' (seg_rom SEGS)) md' HB HJ HFR HMO).
  destruct (c0_land_all i cx fp k acc ly3 S3 W3 ms m' regs' pc0 C0P_L pos r fab op nm bs xs rs HB HF HX Hnm HK HR)
    as (HC & HNM & HARG).
  exists pos, r, fab, op, nm, bs.
  split; [exact HC|]. split; [exact HNM|].
  split; [exact (c0_reg_keep cx fp W3 xs rs ms (mkst regs' (Z_to_bv 64 (BASE + C0P_L)) m' (seg_rom SEGS)) HK r bs Hr HREG)|].
  split; [exact HARG|]. split; [exact S60|]. split; [exact S20|]. split; [exact Hok|]. split; [exact Hn5|].
  split; [exact Hb0|]. split; [exact Hj|]. split; [exact Hlf|]. split; [exact G19 | exact G24].
Qed.

Lemma c0_to_lr : forall POST i j cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte) md'
  (regs' : bvmap 5 word) pc0 pos r fab op nm bs xs rs,
  lx_from B MT POST (C0_LR B MT i j) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m' md' k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c0_from i cx fp k acc ly3 S3 W3 ms pc0 pos r fab op nm bs -> lreg W3 ms r bs ->
  Forall (fun x => x = 0x20 \/ x = 0x60) xs -> In (r, LX_REG) rs -> In (nm, c0_nk (lc_pl cx) pos + 1) rs ->
  c0_kept cx fp W3 xs rs (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x20) = Some (2 ^ 64 - 1) ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x60) = Some nm ->
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab -> Boxreg.bx_n bs < 5 ->
  c0_basev (lc_pl cx) pos < 0 -> 0 <= j <= fab - c0_nchv (lc_pl cx) pos ->
  (forall b, 0 <= b < j -> ~ range_free_c.range_free_ok bs b (c0_nchv (lc_pl cx) pos) fab) ->
  ((range_free_c.range_free_ok bs j (c0_nchv (lc_pl cx) pos) fab /\ getr regs' 10 = w64 1) \/
   (~ range_free_c.range_free_ok bs j (c0_nchv (lc_pl cx) pos) fab /\ getr regs' 10 = w64 0)) ->
  c0_regs cx fp regs' r fab op pos -> getr regs' 19 = w64 j ->
  getr regs' 24 = w64 (fab - c0_nchv (lc_pl cx) pos + 1) ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C0P_LR)) m' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros POST i j cx fp k acc ly3 S3 W3 ms m' md' regs' pc0 pos r fab op nm bs xs rs
    HN HB HJ HFR HMO HF HREG HX Hr Hnm HK S20 S60 Hok Hn5 Hb0 Hj Hlf HRES HR G19 G24.
  apply (HN cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + C0P_LR)) m' (seg_rom SEGS)) md' HB HJ HFR HMO).
  destruct (c0_land_all i cx fp k acc ly3 S3 W3 ms m' regs' pc0 C0P_LR pos r fab op nm bs xs rs HB HF HX Hnm HK HR)
    as (HC & HNM & HARG).
  exists pos, r, fab, op, nm, bs.
  split; [exact HC|]. split; [exact HNM|].
  split; [exact (c0_reg_keep cx fp W3 xs rs ms (mkst regs' (Z_to_bv 64 (BASE + C0P_LR)) m' (seg_rom SEGS)) HK r bs Hr HREG)|].
  split; [exact HARG|]. split; [exact S60|]. split; [exact S20|]. split; [exact Hok|]. split; [exact Hn5|].
  split; [exact Hb0|]. split; [exact Hj|]. split; [exact Hlf|]. split; [exact G19|]. split; [exact G24 | exact HRES].
Qed.

End c.
End b.
End a.

Lemma c0k_U_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
  intros E n v c H Hv. unfold U. cbn [sv_denot]. rewrite H. unfold w64. rewrite (unsigned_lit_small v) by exact Hv.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma c0k_wtest : forall n, 0 <= n < 256 -> (38 <? (n + -2) mod 2 ^ 64) = negb ((2 <=? n) && (n <=? 40)).
Proof.
  intros n Hn. destruct (Z.ltb_spec n 2) as [Hlt | Hge].
  - assert (X : (n + -2) mod 2 ^ 64 = n - 2 + 2 ^ 64) by (symmetry; apply (Z.mod_unique _ _ (-1)); lia).
    rewrite X. replace (2 <=? n) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb negb]. apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. replace (2 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.leb_spec n 40); [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.

Lemma c0k_w64_mod : forall x, w64 (x mod 2 ^ 64) = w64 x.
Proof. intros x. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

(* The bytes a run kept, from its frame_of (the windows of the run's regions are the slots xs). *)
Ltac c0k_kd cx fp WW xs rs Ex GEO UB K :=
  lazymatch goal with
  | HFx : frame_of _ _ (mrestrict _ ?m) (mrestrict _ ?m') |- _ =>
    assert (K : c0_kept cx fp WW xs rs m m');
    [ eapply (c0_kept_frame cx fp WW xs rs Ex _ _ _ GEO);
      [ repeat apply Forall_cons; try apply Forall_nil; lia
      | exact HFx
      | let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
        let a := fresh "a" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
        intros bb wlo whi a Hin Hr; vm_compute in Hin;
        repeat (let Hx := fresh "Hx" in destruct Hin as [Hx | Hin];
          [ injection Hx as <- <- <-; cbn [YP09.base_val] in Hr; rewrite UB in Hr;
            first [ lia | apply Exists_cons_hd; lia | apply Exists_cons_tl; apply Exists_cons_hd; lia ] | ]);
        destruct Hin ]
    | ]
  end.

(* The write windows of a run's regions: read-only ones, and spill slots in the function's stack window. *)
Ltac c0k_awr cx UB :=
  cbn [ss_mem add_cond c0k_ss];
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite UB; lia | cbn; unfold LX_STK; lia | cbn; lia |] ].

(* A register goal of a landing, from the register's value prreg gave and the seat's facts (ER: the seat's
   atoms 0 .. 31 are the cut's registers). *)
Ltac c0k_reg_close ER :=
  first
  [ match goal with Q : getr (ms_regs ?m) ?n = ew ?E ?a |- getr (ms_regs ?m) ?n = _ =>
      rewrite Q; first [ rewrite (ER a n eq_refl); assumption | assumption ] end
  | match goal with Q : getr (ms_regs ?m) ?n = _ |- getr (ms_regs ?m) ?n = _ =>
      rewrite Q; first [exact c0k_m1 | reflexivity | assumption] end ].

(* The count s8 of the inlined lowest_free loop (0x80918 .. 0x8092c), as the engine leaves it: d = fab - nch (atoms
   nf and na), s8 = addiw ((-(0 <s d)) & d, 1) = max (d, 0) + 1 (BoxBLxCase1Want.v's cw_s8z). *)
Definition c0k_d (na nf : nat) : sv := SAlu ALU_ADD (SMd M_MUL (SOff na 0) (SLit (-1))) (SOff nf 0).
Definition c0k_s8 (na nf : nat) : sv :=
  SAluw ALU_ADD (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (c0k_d na nf))) (c0k_d na nf)) (SLit 1).
Definition c0k_dz (n f : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_ADD (zcanon (zmd_raw 64 M_MUL (zcanon (n + 0)) (zcanon (-1)))) (zcanon (f + 0))).
Definition c0k_s8z (n f : Z) : Z :=
  bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 ALU_ADD
    (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SUB (zcanon 0)
       (zcanon (zalu_raw 63 64 ALU_SLT (zcanon 0) (c0k_dz n f))))) (c0k_dz n f)) mod 2 ^ 32)
    (zcanon 1 mod 2 ^ 32))).

Lemma c0k_U_s8 : forall E na nf n f, ew E na = w64 n -> ew E nf = w64 f -> 0 <= n < 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
  U E (c0k_s8 na nf) = c0k_s8z n f.
Proof.
  intros E na nf n f Hna Hnf Hn Hf. unfold c0k_s8, c0k_s8z, c0k_dz, c0k_d.
  rewrite U_of_S, S_SAluw, !U_SAlu, !U_SMd, !U_SOff, !U_SLit, Hna, Hnf. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma c0k_s8_val : forall n f, 2 <= n <= 40 -> n <= f <= 40 -> c0k_s8z n f = f - n + 1.
Proof.
  intros n f Hn Hf.
  assert (H : forallb (fun n => forallb (fun f => (f <? n) || (c0k_s8z n f =? f - n + 1))
                (map Z.of_nat (seq 0 41))) (map Z.of_nat (seq 0 41)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (In_n : In n (map Z.of_nat (seq 0 41))).
  { replace n with (Z.of_nat (Z.to_nat n)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H n In_n). rewrite forallb_forall in H.
  assert (In_f : In f (map Z.of_nat (seq 0 41))).
  { replace f with (Z.of_nat (Z.to_nat f)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H f In_f). apply orb_true_iff in H as [H | H]; [apply Z.ltb_lt in H; lia | apply Z.eqb_eq; exact H].
Qed.

Lemma c0k_denot_s8 : forall E na nf n f, ew E na = w64 n -> ew E nf = w64 f -> 2 <= n <= 40 -> n <= f <= 40 ->
  sv_denot E (c0k_s8 na nf) = w64 (f - n + 1).
Proof.
  intros E na nf n f Hna Hnf Hn Hf. rewrite denot_lit_U, (c0k_U_s8 E na nf n f Hna Hnf) by lia.
  rewrite c0k_s8_val by lia. reflexivity.
Qed.

(* After a run: drop its frame facts and the copy of img_env it adds. *)
Ltac c0k_clean :=
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  | H : img_env ?v ?l ?e, H' : img_env ?v ?l ?e |- _ => clear H'
  end.
(* After a run: the bytes it kept, added to the ones kept since the seat (KA). *)
Ltac c0k_step cx fp WW xs rs Ex GEO UB KA :=
  let Kn := fresh "Kn" in c0k_kd cx fp WW xs rs Ex GEO UB Kn;
  let KA' := fresh "KA" in pose proof (c0_kept_trans _ _ _ _ _ _ _ _ KA Kn) as KA'; clear KA Kn; rename KA' into KA;
  c0k_clean.

Lemma c0k_land1 : forall n, Z.land n 1 = (if Z.even n then 0 else 1).
Proof. intros n. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. apply Zmod_even. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

(* A word a region's chunk fixes, where the run stopped at a call (st_ok, not st_ok_pi). *)
Lemma c0k_word_of_st : forall (W3 : world SEGS) E ss (ms : machine_state) i n b lo hi wlo whi cs off e v,
  st_ok SEGS E ss (restrict (w_H W3) ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (b + off) = Some v.
Proof.
  intros W3 E ss ms i n b lo hi wlo whi cs off e v HS Hi Hb Hin He Hv.
  pose proof (st_ok_region_nth E ss (restrict (w_H W3) ms) i _ HS Hi) as HR.
  cbn [restrict ms_mem] in HR.
  exact (lx_word_of_region W3 ms E n b cs lo hi wlo whi off e v HR Hb Hin He Hv).
Qed.

(* The call of range_free (prev, b, nch, fab) from the realigned stack (0x80568 and 0x80940): prev is an object of
   the side-stack frame (in scope at a loop turn, LSH_iter); the callee's contract (lh_range_free through YC85.v
   cl_callS) keeps every byte the phase's facts speak about (lx_keep_call). *)
Lemma c0_rf_call : forall cx fp k ly3 S3 W3 (ms : machine_state) md rs b nch fab bs,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(LX_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun q => exists n, In (fst q, n) (ablocks B ly3 S3) /\ 0 <= snd q <= req_size n) rs ->
  getr (ms_regs ms) 2 = w64 (lsp1 cx) -> getr (ms_regs ms) 8 = w64 (lsp0 cx) ->
  getr (ms_regs ms) 3 = getr (lc_regs cx) 3 -> getr (ms_regs ms) 4 = getr (lc_regs cx) 4 ->
  YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= bv_unsigned (getr (ms_regs ms) 1) ->
  getr (ms_regs ms) 10 = w64 (lF cx fp + 64) -> getr (ms_regs ms) 11 = w64 b ->
  getr (ms_regs ms) 12 = w64 nch -> getr (ms_regs ms) 13 = w64 fab ->
  -2 ^ 31 <= b < 2 ^ 31 -> 1 <= nch <= 40 -> 1 <= fab <= 40 ->
  lsaved cx W3 ms -> lshadow cx fp W3 ms LSH_iter -> lprev cx fp W3 ms bs ->
  length bs = 288%nat -> Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB_range_free)) (ms_mem ms) (seg_rom SEGS)) md)
    (fun W2 c2 => exists regs2 mem2 md2, W2 = W3 /\
       c2 = mkCfg (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
         [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved (ms_regs ms) regs2 /\ lx_keep cx fp W3 rs (ms_mem ms) mem2 /\
       ((range_free_c.range_free_ok bs b nch fab /\ getr regs2 10 = w64 1) \/
        (~ range_free_c.range_free_ok bs b nch fab /\ getr regs2 10 = w64 0))).
Proof.
  intros cx fp k ly3 S3 W3 ms md rs b nch fab bs HB HJ HFR Hbl Hrs G2 G8 G3 G4 Hra Hra4 H10 H11 H12 H13
    Hb Hnch Hfab HSAVED HSH HPREV HLEN HB1 HB2 HB3.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ) as EFA.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HFal & HSHeq).
  set (E := lx_env cx fp (ms_regs ms) []).
  assert (E32 : ew E 32 = w64 SHADOW_OFF) by exact (lx_env_x cx fp (ms_regs ms) [] 0 ltac:(lia)).
  assert (E46 : ew E 46 = w64 (lF cx fp)) by exact (lx_env_x cx fp (ms_regs ms) [] 14 ltac:(lia)).
  assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (U46 : U E (SOff LA_F 0) = lF cx fp) by (apply (U_atom E 46 (lF cx fp) E46); lia).
  assert (HOBJ : afobj SEGS B ly3 S3 W3 (ms_mem ms) (lF cx fp + 64) 288).
  { split; [|split].
    - exists LX_CID, fp. split; [rewrite HFR; left; reflexivity|]. split; [unfold LX_CID; lia|].
      rewrite EFA. split; [apply Z.mod_divide in HFal; [|lia]; destruct HFal as [z ->]; apply Z.mod_divide; [lia|]; exists (8 * z); lia|].
      split; [lia|]. change (fs_frame_bytes LX_CID) with 512. lia.
    - apply Z.mod_divide in HFal; [|lia]. destruct HFal as [z ->]. apply Z.mod_divide; [lia|]. exists (8 * z + 8). lia.
    - pose proof (lx_shent_frame B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR E 64 352 U32 U46 HSH ltac:(right; lia))
        as (HRA & _).
      cbn [she_m she_lo she_hi] in HRA. rewrite U32, U46 in HRA.
      rewrite (aview_rd_of SEGS). replace 288 with (352 - 64) by lia. exact HRA. }
  pose proof (lh_range_free B MT HY) as RF.
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & MOK & HNEED & HTR).
  pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HJ as (HARc & Hlyc & _).
  assert (ESPc : spZ (ms_regs ms) = lsp0 cx + (lsp1 cx - lsp0 cx)).
  { unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (ES0c : s0Z (ms_regs ms) = lsp0 cx).
  { unfold s0Z. rewrite G8. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HSAVED as (HRA8 & HSJ).
  pose proof (HSJ 0 ltac:(lia)) as HS016. cbn [Z.ltb Z.compare] in HS016.
  replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in HS016 by lia.
  assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx + (lsp1 cx - lsp0 cx)) (s0Z (ms_regs ms)) (lch cx)).
  { replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
    rewrite ES0c. apply (c0k_achain_ly (lc_ly cx)); [exact (c0k_layout_top _ _ _ Hlyc)|].
    apply (lx_achain cx _ (lsp1 cx)); [exact Hch | lia | lia | apply c0k_mod8; exact Hal16 | exact Hra40
      | intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)
      | unfold lview in HRA8; exact HRA8 | unfold lview in HS016; exact HS016 | lia]. }
  rewrite pa_sigma_range_free.
  eapply SRr_mono.
  { eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
      (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k RANGE_FREE_STKB [] 0 (lsp1 cx - lsp0 cx) _ (lch cx)
      (fun ly' S' W' (regs' : bvmap 5 word) mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         ((range_free_c.range_free_ok bs b nch fab /\ getr regs' 10 = w64 1) \/
          (~ range_free_c.range_free_ok bs b nch fab /\ getr regs' 10 = w64 0))) HJ).
    - exact ESPc.
    - pose proof (proj1 (Z.mod_divide (lsp1 cx) 32 ltac:(lia)) Hsp1al) as [q1 Hq1].
      pose proof (proj1 (Z.mod_divide (lsp0 cx) 16 ltac:(lia)) Hsp0al) as [q2 Hq2].
      rewrite Hq1, Hq2. replace (q1 * 32 - q2 * 16) with ((2 * q1 - q2) * 16) by lia. apply Z_mod_mult.
    - lia.
    - unfold RANGE_FREE_STKB, ESTACK. lia.
    - unfold RANGE_FREE_STKB, ESTACK, LX_STK. lia.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - reflexivity.
    - exact Hra.
    - exact Hra4.
    - exact HCH.
    - intros HPREc.
      exact (RF ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (lch cx) (lF cx fp + 64) b nch fab bs HPREc
        H10 H11 H12 H13 Hb Hnch Hfab HOBJ HLEN (fun j Hj => HPREV j Hj) HB1 HB2 HB3).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & HRES)).
  exists regs2, mem2, md2. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact HP|]. split; [|exact HRES].
  eapply (lx_keep_call B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR rs RANGE_FREE_STKB).
  - lia.
  - exact Hbl.
  - exact Hrs.
  - replace (lsp1 cx) with (lsp0 cx + (lsp1 cx - lsp0 cx)) by lia. exact HJc.
Qed.

End d.

(* A callee-saved register after a call: as before it (aregs_preserved). *)
Ltac c0k_pres HP :=
  lazymatch type of HP with aregs_preserved ?r1 ?r2 =>
  lazymatch goal with |- getr r2 ?n = _ =>
    let z := eval vm_compute in (bv_unsigned n) in
    let T := fresh "T" in
    assert (T : getr r2 n = getr r1 n) by exact (HP z ltac:(unfold acallee_saved; lia));
    rewrite T; clear T end end.
