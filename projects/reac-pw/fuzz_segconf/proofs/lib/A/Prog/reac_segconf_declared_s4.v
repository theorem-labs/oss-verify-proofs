(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): one pass of the member loop, from the loop head KL
   (0x8e234) at pass j: the inline load8 check of &tok[2 + j] (0x8e234-0x8e238), the call of number at 0x8e244
   (through cl_callS_wide, PaNoChain.v) that writes ids[j] in this walk's class-3 side-stack frame, the refusal edge
   `beqz a0` at 0x8e248 (to KR, 0x8e278), the advance 0x8e24c-0x8e25c and `bnez s11` at 0x8e260, which re-enters
   KL at pass j + 1 or falls through to KD (0x8e264). The symbolic machinery (the cut-point seed, the call, the
   re-seat after it) is the one of the sibling segment chain_words_s2.v (KC -> KL 0), which walks the same inline
   check and the same call once, for the first word; its lemmas are copied here with the prefix cw3_ and generalised
   over the pass index. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s3.v, with its module paths and module names changed; 333 of its 402 lines of code are new or changed and 804 lines of the source are left out. *)
(* Segment 4 of the walk of reac_segconf_declared (fuzz_segconf.asan, image A; the interface is
   reac_segconf_declared_d.v): the latch of the loop over c->seg, from the cut KT (0x89a34) at pass i to the loop
   head KL (0x899c0) at pass i + 1 or to the join KX (0x89a78). The stretch: the inline check of c->n
   (0x89a34-0x89a38: lb of its shadow byte through s5, bnez to the slow path at 0x89a64), the reload of c->n (lw at
   0x89a3c), the advance of s7, s9, s6 (0x89a40-0x89a48), blt s7, a0 (0x89a4c) and the j at 0x89a50. The check
   passes on the token engine's whole-granule arm (the slow path begins with an ld, not an andi): its obligation is
   the 8-byte granule of c + 0x2c80, which the allocator invariant gives for c's live block. The stretch writes
   nothing, so the frame part, the kept part and the table carry over unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at KT: s8 = &c->n (atom 24) with c->n's 4 bytes (atom 33) in the one region, the shadow base
   (atom 32), s5 = the shadow byte of s8 written as (s8 >> 3) + base, so that the lb of 0x89a34 reads a shadow
   entry and the engine takes the token route; no shadow knowledge is seeded *)
Definition dcs4_Bx : sv := SOff 32 0.
Definition dcs4_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 0) (SLit 3)) (SOff 32 0).
Definition dcs4_nR : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition dcs4_facts : facts := mkFacts [(24%nat, mkAF 4096 (2 ^ 47 - 32) 3); (32%nat, mkAF SB SB 0)] [] [].
Definition dcs4_ss : sstate := mkSS DC_KT (sr_set sr_atoms 21 dcs4_shx) [dcs4_nR] None dcs4_facts.
Definition dcs4_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition dcs4_SH : list shent := [].

Lemma dcs4_val_mem : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dcs4_aview_ext : forall segs H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma dcs4_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
(* the shadow address the loop keeps in s5 *)
Lemma dcs4_shadow_denot : forall E n m x, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 SB -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SB + x / 8).
Proof.
intros E n m x Hn Hm Hx. cbn [sv_denot]. rewrite Hn, Hm, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id x) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hx8 : 0 <= x / 8 < M64) by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(zcanon_id (x / 8) Hx8).
rewrite !(zcanon_id SB) by (unfold SB, M64; lia). f_equal. lia.
Qed.
(* the 4 bytes of a u32 field of a byte block are sa_val of its value *)
Lemma dcs4_nth_fld : forall (bs : list byte) o n k d, (k < n)%nat ->
  nth k (firstn n (skipn o bs)) d = nth (o + k) bs d.
Proof.
induction bs as [|x bs IH]; intros o n k d Hk.
- rewrite skipn_nil, firstn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
- destruct o as [|o].
  + destruct n as [|n]; [lia|]. destruct k as [|k]; cbn [skipn firstn nth Nat.add]; [reflexivity|].
    specialize (IH 0%nat n k d ltac:(lia)). cbn [skipn Nat.add] in IH. exact IH.
  + cbn [skipn]. rewrite IH by exact Hk. reflexivity.
Qed.
Lemma dcs4_u32_val : forall (rd : reader) a bs off v, sa_bytes rd a bs -> 0 <= off ->
  off + 4 <= Z.of_nat (length bs) -> seg_spec.u32_enc v (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 v.
Proof.
intros rd a bs off v Hb Hoff Hlen [Hv Hf]. unfold sa_val. intros k Hk.
assert (Hi : (Z.to_nat off + k < length bs)%nat) by lia.
pose proof (Hb _ Hi) as E. rewrite Nat2Z.inj_add, Z2Nat.id in E by lia.
replace (a + (off + Z.of_nat k)) with (a + off + Z.of_nat k) in E by lia. rewrite E. f_equal.
rewrite <- (dcs4_nth_fld bs (Z.to_nat off) 4 k ZB0 Hk).
change (firstn 4 (skipn (Z.to_nat off) bs)) with (seg_spec.fldz off 4 bs). rewrite Hf.
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
rewrite (nth_error_nth _ _ _ (YN01.nth_error_Z_to_le_bytes 4 _ k Hk)).
assert (Ev : bv_unsigned (Z_to_bv 64 v) = v) by (apply unsigned_lit_small; lia). rewrite Ev.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbv [YG0f.le_byte YO0f.le_byte]. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
(* blt on two small non-negative values *)
Lemma dcs4_blt : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. unfold U in Ha, Hb.
change (branch_taken BC_LT (sv_denot E a) (sv_denot E b)) with (c_lts (sv_denot E a) (sv_denot E b)).
rewrite c_lts_small by lia. unfold bv_ltu. rewrite Ha, Hb. reflexivity.
Qed.
(* lw sign-extends c->n, a small non-negative value *)
Lemma dcs4_sext_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v He Hv. rewrite U_SExt, (U_atom E n v He) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
(* a run over read-only regions writes nothing *)
Lemma dcs4_frame_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' H Hro x. apply H. intros (r & Hr & Ha).
rewrite forallb_forall in Hro. pose proof (Hro r Hr) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition dcs4_E (regs : bvmap 5 word) (nn : Z) : env := Eimg (Ereg regs [w64 SB; w64 nn]).
Lemma dcs4_seed : forall (W : world SEGS) mem (regs : bvmap 5 word) X nn,
  getr regs 24 = w64 X -> getr regs 21 = w64 (SB + X / 8) ->
  4096 <= X <= 2 ^ 47 - 32 -> X mod 8 = 0 -> 0 <= nn < 2 ^ 32 ->
  sa_val (rdW W mem) X 4 nn ->
  st_ok_pi SEGS VAL (dcs4_E regs nn) dcs4_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_KT)) mem (seg_rom SEGS))) /\
  sh_ok SEGS dcs4_Bx dcs4_SH (dcs4_E regs nn) (mrestrict (w_H W) mem).
Proof using.
intros W mem regs X nn H24 H21 HX HX8 Hnn HV.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (dcs4_E regs nn) m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold dcs4_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew (dcs4_E regs nn) 32 = w64 SB)
  by (unfold dcs4_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (X33 : ew (dcs4_E regs nn) 33 = w64 nn)
  by (unfold dcs4_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E24 : ew (dcs4_E regs nn) 24 = Z_to_bv 64 X) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (U24 : base_val (dcs4_E regs nn) (Some 24%nat) = X).
{ cbn [base_val]. rewrite E24. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok, dcs4_SH; apply Forall_nil].
rewrite restrict_mkst_fx. unfold dcs4_ss. apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [unfold dcs4_E; apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite H21. unfold dcs4_shx. symmetry. apply (dcs4_shadow_denot _ 24 32 X E24 X32). lia.
- vm_compute. reflexivity.
- unfold dcs4_nR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  apply (chunk_ok_val SEGS (dcs4_E regs nn) _ X 0 4 (SOff 33 0) nn);
    [cbn [sv_denot]; rewrite X33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | lia | rewrite Z.add_0_r; exact (dcs4_val_mem SEGS (w_H W) mem _ 4%nat nn HV)].
- apply pairwise_disjoint_of_extents. unfold dcs4_nR, extent_of_region. cbn. repeat constructor.
- split; [|split; [exact I | exact I]].
  cbn [dcs4_facts f_atoms atoms_ok].
  split; [apply (dcs4_afact _ 24%nat X); [exact E24 | lia | lia | change (2 ^ 3) with 8; exact HX8 | lia]|].
  split; [apply (dcs4_afact _ 32%nat SB); [exact X32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I.
Qed.
(* the table and the count cell carry over a run that writes nothing *)
Lemma dcs4_tab_ext : forall c ti (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
  dc_tab c ti W m -> dc_tab c ti W m'.
Proof using.
intros c ti W m m' He (H1 & H2 & H3 & H4).
split; [|split; [|split; [exact H3 | exact H4]]].
- destruct H1 as (bs & Hb & Henc). exists bs. split; [|exact Henc].
  intros j Hj. rewrite (dcs4_aview_ext SEGS (w_H W) m m' He). exact (Hb j Hj).
- intros kk Hk. rewrite (dcs4_aview_ext SEGS (w_H W) m m' He). exact (H2 kk Hk).
Qed.
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac dcs4_awr_ro :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac dcs4_mdv nm := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.

(* the frame part of a cut carried over a run that writes nothing and keeps the registers the frame part names *)
Lemma dcs4_fi_ext : forall c k ly S W regs (m : word -> option byte) md regs' m' md',
  dc_fi B STK_reac_segconf_declared c k ly S W regs m md ->
  ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)]
    ly S W m' md' k ->
  (forall x, m' x = m x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 20 = getr regs 20 ->
  dc_fi B STK_reac_segconf_declared c k ly S W regs' m' md'.
Proof using.
intros c k ly S W regs m md regs' m' md' [J1 G2 G3 G4 G8 G9 G19 G20 GSV G16 G24 GT GM GN GFL] HJ He
  E2 E3 E4 E8 E9 E19 E20.
assert (RD : forall a, rdword (rdW W m') a = rdword (rdW W m) a).
{ intros a. apply rdword_ext. intros kk Hk. apply (dcs4_aview_ext SEGS (w_H W) m m' He). }
constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E19; exact G19.
- rewrite E20; exact G20.
- intros j r Hj. rewrite RD. exact (GSV j r Hj).
- rewrite RD; exact G16.
- rewrite RD; exact G24.
- rewrite RD; exact GT.
- rewrite RD; exact GM.
- rewrite RD; exact GN.
- rewrite RD; exact GFL.
Qed.
(* c->n at a cut: the entry's bytes (sa_rconf), kept by the journal's block clause (c's block is live at both
   ends, dc_un's permutation, and the footprint misses it, dc_pre's two sa_disj conjuncts) *)
Lemma dcs4_n_kt : forall c ly3 S3 W3 mem3 md3 k,
  dc_pre B STK_reac_segconf_declared RLO RHI GOTW GUARD c ->
  ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)]
    ly3 S3 W3 mem3 md3 k ->
  dc_un B c ly3 S3 ->
  sa_val (rdW W3 mem3) (x_c c + DC_RC_N) 4 (dc_nn c) /\ (length (dc_segs c) <= 32)%nat.
Proof using.
intros c ly3 S3 W3 mem3 md3 k HP HJ HU.
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & (bs & Hbs & Hlen & Hle32 & _ & Hn & _) & (pb & nb & Hin & Hp1 & Hp2) & _ & HVT & HD1 & HD2 & _).
destruct HVT as (_ & _ & _ & Htbmax & _).
split; [|exact Hle32].
pose proof (dcs4_u32_val _ _ bs seg_spec.RC_N _ Hbs ltac:(unfold seg_spec.RC_N; lia)
  ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia) Hn) as HV0.
pose proof HU as [HPERM _ _].
assert (Hin3 : In (pb, nb) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
assert (L : (length (x_tb c) <= length (snd (dc_res c)))%nat /\ Z.of_nat (length (snd (dc_res c))) <= x_max c)
  by exact (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Htbmax)).
destruct L as [L1 L2].
unfold seg_spec.SEG_C_SIZE in Hp2. unfold sa_disj, seg_spec.SEG_C_SIZE, seg_spec.RVLAN_SIZE in HD1, HD2.
unfold sa_val in HV0 |- *. intros kk Hk.
replace (x_c c + DC_RC_N + Z.of_nat kk) with (pb + (x_c c + DC_RC_N + Z.of_nat kk - pb)) by lia.
rewrite (K2 pb nb _ Hin Hin3).
- replace (pb + (x_c c + DC_RC_N + Z.of_nat kk - pb)) with (x_c c + seg_spec.RC_N + Z.of_nat kk)
    by (unfold DC_RC_N, seg_spec.RC_N; lia).
  exact (HV0 kk Hk).
- unfold req_size. destruct (Z.eqb_spec nb 0); unfold DC_RC_N; lia.
- intros (r & Hr & Ha). unfold dc_FP, declared_W, vtab_W in Hr. unfold DC_RC_N in Ha.
  apply in_app_or in Hr as [Hr | Hr].
  + destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in Ha.
    destruct HD1 as [HD1 | HD1]; lia.
  + destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|destruct Hr].
    destruct Hr as [<- | []]. cbn [fst snd] in Ha. destruct HD2 as [HD2 | HD2]; lia.
Qed.
(* the shadow of c's live block: the allocator invariant at the cut *)
Lemma dcs4_ra : forall ly S W mem md pb nb a, AR SEGS B ly S W mem md -> In (pb, nb) (ablocks B ly S) ->
  pb <= a -> a + 8 <= pb + req_size nb -> range_addressable (rdW W mem) SHADOW_OFF a 8.
Proof using LAWS.
intros ly S W mem md pb nb a HAR Hin H1 H2.
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as [HBS _].
exact (block_shadow_range _ _ _ _ _ _ HBS H1 H2).
Qed.

Lemma dc_S4 : dc_S4P B STK_reac_segconf_declared RLO RHI GOTW GUARD.
Proof using LAWS RUN RUNTO BR.
intros c i HPRE HKL HKX. unfold from_KT, dc_from.
intros ti added ly3 S3 W3 regs3 mem3 md3 (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F19 F20 FSV F16 F24 FTB FMX FN FFL].
pose proof HLR as (R23 & R22 & R25 & R24 & R21 & R26 & R27 & R18).
pose proof HPRE as [HAFN _ _ HC64 _ _ _ _ _ _ HDP _ _].
destruct HDP as (Hc0 & Hc16 & _ & (pb & nb & Hin & Hp1 & Hp2) & _).
pose proof HUN as [HPERM _ _].
assert (Hin3 : In (pb, nb) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
pose proof (proj1 HJ) as HAR3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpc & _).
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_C_SIZE in Hp2.
assert (Hreq : req_size nb = nb) by (unfold req_size; destruct (Z.eqb_spec nb 0); [lia | reflexivity]).
rewrite Hreq in Hpc.
destruct (dcs4_n_kt c ly3 S3 W3 mem3 md3 0 HPRE HJ HUN) as [HNV Hle32].
assert (HX : 4096 <= x_c c + DC_RC_N <= 2 ^ 47 - 32) by (unfold DC_RC_N; lia).
assert (HX8 : (x_c c + DC_RC_N) mod 8 = 0) by (unfold DC_RC_N; clear - Hc16; Z.div_mod_to_equations; lia).
assert (Hnn : 0 <= dc_nn c <= 32) by (unfold dc_nn; lia).
assert (Hii : Z.of_nat i < dc_nn c) by (unfold dc_nn; lia).
assert (HRA8 : range_addressable (rdW W3 mem3) SHADOW_OFF (x_c c + DC_RC_N) 8)
  by (apply (dcs4_ra ly3 S3 W3 mem3 md3 pb nb); [exact HAR3 | exact Hin3 | unfold DC_RC_N; lia
     | rewrite Hreq; unfold DC_RC_N; lia]).
destruct (dcs4_seed W3 mem3 regs3 (x_c c + DC_RC_N) (dc_nn c) R24 R21 HX HX8 ltac:(lia) HNV) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (dcs4_E regs3 (dc_nn c))) by (unfold dcs4_E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (dcs4_E regs3 (dc_nn c)) m = getr regs3 rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold dcs4_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew (dcs4_E regs3 (dc_nn c)) 32 = w64 SB)
  by (unfold dcs4_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (X33 : ew (dcs4_E regs3 (dc_nn c)) 33 = w64 (dc_nn c))
  by (unfold dcs4_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (UB : U (dcs4_E regs3 (dc_nn c)) dcs4_Bx = SHADOW_OFF)
  by (unfold dcs4_Bx; rewrite (U_atom _ 32 SB X32) by (unfold SB; lia); reflexivity).
assert (U24 : U (dcs4_E regs3 (dc_nn c)) (SOff 24 0) = x_c c + DC_RC_N)
  by (apply U_atom; [rewrite (EEo 24%nat 24%bv eq_refl); exact R24 | lia]).
unfold cfg_at, w64.
(* 0x89a34 .. 0x89a4c: the inline check of c->n (whole-granule arm), the reload, the advance, to blt *)
paj_run_tok RUN HS HJ SHOK dcs4_Bspan.
{ rewrite U24. eapply (obl_of_range SEGS _ _ _ _ _ 8 (x_c c + DC_RC_N) 8); [exact HRA8 | exact UB | lia | lia]. }
{ dcs4_awr_ro. }
try dcs4_mdv mdk.
lazymatch type of HS with context [restrict _ ?m] => rename m into msa end.
pose proof (dcs4_frame_ro _ _ _ _ HF eq_refl) as HEQa.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK dcs4_Bspan.
- (* blt taken: KL at pass i + 1 *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
  lazymatch type of Hbr with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (E23 : ew Ex 23 = Z_to_bv 64 (Z.of_nat i))
      by (rewrite ew_ewset_other by lia; rewrite (EEo 23%nat 23%bv eq_refl); exact R23);
    assert (E33 : ew Ex 33 = Z_to_bv 64 (dc_nn c)) by (rewrite ew_ewset_other by lia; exact X33);
    rewrite (dcs4_blt Ex _ _ (Z.of_nat i + 1) (dc_nn c) (U_atom_off Ex 23 (Z.of_nat i) 1 E23 ltac:(lia) ltac:(lia))
      (dcs4_sext_U Ex 33 (dc_nn c) E33 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hbr
  end.
  apply Z.ltb_lt in Hbr.
  paj_run_to_tok RUNTO HS HJ SHOK dcs4_Bspan DC_KL.
  { dcs4_awr_ro. }
  try dcs4_mdv mdk2.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msb end.
  pose proof (dcs4_frame_ro _ _ _ _ HF eq_refl) as HEQb.
  assert (HEQ2 : forall x, ms_mem msb x = mem3 x) by (intros x; rewrite HEQb; exact (HEQa x)).
  clear HF HFr HG.
  assert (T21 : getr (ms_regs msb) 21 = w64 (SB + (x_c c + DC_RC_N) / 8)).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) =>
      pose proof (st_ok_pi_restrict_reg H Ex ss msx (21%bv : bv 5) HS) as Q;
      let e := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
      change (sr_get (ss_regs ss) (21%bv : bv 5)) with e in Q;
      assert (Q24 : ew Ex 24 = Z_to_bv 64 (x_c c + DC_RC_N))
        by (rewrite ew_ewset_other by lia; rewrite (EEo 24%nat 24%bv eq_refl); exact R24);
      assert (Q32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ew_ewset_other by lia; exact X32);
      rewrite Q; exact (dcs4_shadow_denot Ex 24 32 _ Q24 Q32 ltac:(lia)) end. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (18%bv : bv 5) T18. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25.
  rewrite (EEo 2%nat 2%bv eq_refl) in T2. rewrite (EEo 3%nat 3%bv eq_refl) in T3.
  rewrite (EEo 4%nat 4%bv eq_refl) in T4. rewrite (EEo 8%nat 8%bv eq_refl) in T8.
  rewrite (EEo 9%nat 9%bv eq_refl) in T9. rewrite (EEo 19%nat 19%bv eq_refl) in T19.
  rewrite (EEo 20%nat 20%bv eq_refl) in T20. rewrite (EEo 18%nat 18%bv eq_refl) in T18.
  rewrite (EEo 26%nat 26%bv eq_refl) in T26. rewrite (EEo 27%nat 27%bv eq_refl) in T27.
  rewrite (EEo 22%nat 22%bv eq_refl), R22 in T22. rewrite (EEo 23%nat 23%bv eq_refl), R23 in T23.
  rewrite (EEo 24%nat 24%bv eq_refl) in T24. rewrite (EEo 25%nat 25%bv eq_refl), R25 in T25.
  unfold w64 in T22, T23, T25. unfold DC_IGN in R25, T25.
  rewrite unsigned_lit_small in T22 by lia. rewrite unsigned_lit_small in T23 by lia.
  rewrite unsigned_lit_small in T25 by lia.
  pose proof (dcs4_fi_ext c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs msb) (ms_mem msb) _ HFI HJ HEQ2
    T2 T3 T4 T8 T9 T19 T20) as HFIk.
  pose proof (dcs4_tab_ext c ti W3 mem3 (ms_mem msb) HEQ2 HTAB) as HTABk.
  assert (H56k : rdword (rdW W3 (ms_mem msb)) (dc_s1 c + 56) = Some added).
  { rewrite <- H56. apply rdword_ext. intros kk Hk. apply (dcs4_aview_ext SEGS (w_H W3) mem3 (ms_mem msb) HEQ2). }
  pmkst HS.
  unfold from_KL, dc_from in HKL.
  apply (HKL ti added ly3 S3 W3 (ms_regs msb) (ms_mem msb) _). unfold INV_KL.
  split; [exact HFIk|]. split; [exact HUN|]. split; [exact HTABk|].
  split; [unfold dc_nn in Hbr; lia|]. split; [exact HLOOP|].
  split; [|exact H56k].
  unfold dc_lregs. rewrite Nat2Z.inj_succ.
  split; [rewrite T23; unfold w64; f_equal; lia|].
  split; [rewrite T22; unfold w64; f_equal; lia|].
  split; [rewrite T25; unfold w64, DC_IGN; f_equal; lia|].
  split; [rewrite T24; exact R24|].
  split; [exact T21|].
  split; [rewrite T26; exact R26|].
  split; [rewrite T27; exact R27|].
  rewrite T18; exact R18.
- (* blt not taken: KX, every entry passed *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
  lazymatch type of Hbr with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (E23 : ew Ex 23 = Z_to_bv 64 (Z.of_nat i))
      by (rewrite ew_ewset_other by lia; rewrite (EEo 23%nat 23%bv eq_refl); exact R23);
    assert (E33 : ew Ex 33 = Z_to_bv 64 (dc_nn c)) by (rewrite ew_ewset_other by lia; exact X33);
    rewrite (dcs4_blt Ex _ _ (Z.of_nat i + 1) (dc_nn c) (U_atom_off Ex 23 (Z.of_nat i) 1 E23 ltac:(lia) ltac:(lia))
      (dcs4_sext_U Ex 33 (dc_nn c) E33 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hbr
  end.
  apply Z.ltb_ge in Hbr.
  assert (Hlen : S i = length (dc_segs c)) by (unfold dc_nn in Hbr, Hii; lia).
  destruct HLOOP as [HL1 HL2]. rewrite Hlen, dcl_go_end in HL1.
  assert (Hres : dc_res c = (added, ti)) by (unfold dc_res; rewrite <- HL1; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK dcs4_Bspan DC_KX.
  { dcs4_awr_ro. }
  try dcs4_mdv mdk2.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msb end.
  pose proof (dcs4_frame_ro _ _ _ _ HF eq_refl) as HEQb.
  assert (HEQ2 : forall x, ms_mem msb x = mem3 x) by (intros x; rewrite HEQb; exact (HEQa x)).
  clear HF HFr HG.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  rewrite (EEo 2%nat 2%bv eq_refl) in T2. rewrite (EEo 3%nat 3%bv eq_refl) in T3.
  rewrite (EEo 4%nat 4%bv eq_refl) in T4. rewrite (EEo 8%nat 8%bv eq_refl) in T8.
  rewrite (EEo 9%nat 9%bv eq_refl) in T9. rewrite (EEo 19%nat 19%bv eq_refl) in T19.
  rewrite (EEo 20%nat 20%bv eq_refl) in T20.
  pose proof (dcs4_fi_ext c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs msb) (ms_mem msb) _ HFI HJ HEQ2
    T2 T3 T4 T8 T9 T19 T20) as HFIk.
  pose proof (dcs4_tab_ext c ti W3 mem3 (ms_mem msb) HEQ2 HTAB) as HTABk.
  assert (H56k : rdword (rdW W3 (ms_mem msb)) (dc_s1 c + 56) = Some added).
  { rewrite <- H56. apply rdword_ext. intros kk Hk. apply (dcs4_aview_ext SEGS (w_H W3) mem3 (ms_mem msb) HEQ2). }
  pmkst HS.
  unfold from_KX, dc_from in HKX.
  apply (HKX ly3 S3 W3 (ms_regs msb) (ms_mem msb) _). unfold INV_KX. rewrite Hres. cbn [fst snd].
  split; [exact HFIk|]. split; [exact HUN|]. split; [exact HTABk|].
  rewrite Z.mod_small by lia. exact H56k.
Qed.
End e.
End f.
End d.
