(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDK_HEAD : Z := 0x83d4c.
Definition LDK_G1 : Z := 0x83d94.
Definition LDK_U1 : Z := 0x83d98.
Definition LDK_G2 : Z := 0x83df0.
Definition LDK_U2 : Z := 0x83df4.
Definition LDK_G3 : Z := 0x83e48.
Definition LDK_U3 : Z := 0x83e4c.
Definition LDK_G4 : Z := 0x83e98.
Definition LDK_U4 : Z := 0x83e9c.
Definition LDK_S5 : Z := 0x83ee0.
Definition LDK_BR : Z := 0x83eec.
Definition LDK_EXIT : Z := 0x83f90.
Definition LDK_RO : Z := 0x10390.
Definition LDK_CLOB0 : list (bv 5) := [1; 6; 10; 13; 21]%bv.
Definition LDK_KEEP : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDK_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDK_CLOB : list (bv 5) := [1; 6; 10; 13; 21; 24; 26; 27]%bv.
Definition LDK_KEEPL : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 20; 22; 23; 25; 28; 29; 30; 31]%bv.
Definition LDK_KEEP0 : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma ldk_keep_cases : forall r : bv 5, In r LDK_KEEP -> r = 20%bv \/ In r LDK_KEEP0.
Proof. intros r H. cbv [LDK_KEEP In] in H. cbv [LDK_KEEP0 In]. repeat (destruct H as [<-|H]; [tauto|]). destruct H. Qed.
Lemma ldk_clob_cases : forall r : bv 5, reg_in r LDK_CLOB = false -> r = 0%bv \/ In r LDK_KEEPL.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma ldk_keepl_keep : forall r : bv 5, In r LDK_KEEPL -> In r LDK_KEEP.
Proof. intros r H. cbv [LDK_KEEPL In] in H. cbv [LDK_KEEP In]. repeat (destruct H as [<-|H]; [tauto|]). destruct H. Qed.
Lemma ldk_ro_present : forall (H : word -> bool) (m : word -> option byte) i, 0 <= i < 8 -> exists b, mbyte trasegs (mrestrict H m) (LDK_RO + i) = Some b.
Proof.
intros H m i Hi. unfold mbyte, mrestrict.
assert (Hrom : exists b, seg_rom trasegs (Z_to_bv 64 (LDK_RO + i)) = Some b).
{ assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; eexists; reflexivity. }
destruct (H (Z_to_bv 64 (LDK_RO + i))); [exact Hrom|]. destruct (m (Z_to_bv 64 (LDK_RO + i))) as [b|]; [exists b; reflexivity | exact Hrom].
Qed.
Section e.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HFW : forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i).
Definition ldk_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 31 = w64 flt /\ getr regs 25 = w64 SB.
Definition LDK_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc lo hi : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
ldk_base fy' regs' mem' md' /\
(forall r : bv 5, In r LDK_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDK_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma ldk_env : forall fy regs mem md, ldk_base fy regs mem md ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF]. repeat split; try assumption; lia.
Qed.
Lemma ldk_cell4 : forall x, flt mod 16 = 0 -> (flt + 4 * x) mod 4 = 0.
Proof.
intros x H16. replace (flt + 4 * x) with (flt + x * 4) by lia. rewrite Z.mod_add by lia.
pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
Lemma ldk_cell_val : forall fy regs mem md x, ldk_base fy regs mem md -> 0 <= x -> 4 * x + 4 <= nF ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * x) 4 v.
Proof.
intros fy regs mem md x HB Hx Hlen. pose proof (ldk_env fy regs mem md HB) as (_ & _ & _ & QnF & _).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
apply (val_mem_of_present4 trasegs). intros i Hi.
destruct (proj1 (Hfpres (flt + 4 * x + i) ltac:(clear - Hi Hx Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity.
Qed.
Definition ldk_Bx : sv := SOff 25 0.
Definition ldk_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Local Ltac ldk_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Local Ltac ldk_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Definition ldk_sh20 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 12 0) (SLit 3)) (SOff 25 0).
Definition ldk0_regs := sr_set sr_atoms 20%bv ldk_sh20.
Definition ldk0_mem : smem :=
[ YQ0b.mkRegion (Some 12%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))];
YQ0b.mkRegion (Some 36%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 37 0))] ].
Definition ldk0_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 26 0) (SLit 2)) (SOff 31 0), SOff 36 0);
(SAlu ALU_ADD (SOff 27 0) (SMd M_MUL (SOff 32 0) (SLit 3)), SOff 33 0) ].
Definition ldk0_facts : facts :=
mkFacts [ (12%nat, mkAF 4096 140737479966720 0); (26%nat, mkAF 0 (2^29) 0); (27%nat, mkAF 4096 140737479966720 0);
(31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 140737479966720 0);
(34%nat, mkAF 0 255 0); (36%nat, mkAF 4096 140737479966720 2); (37%nat, mkAF 0 (2^32 - 1) 0) ] [] ldk0_alias.
Definition ss_LDK0x : sstate := mkSS LDK_HEAD ldk0_regs ldk0_mem None ldk0_facts.
Definition ldk0_SH : list shent := [ mkSHE 12 0 1; mkSHE 36 0 4 ].
Section S0.
Variables (pb pn pix palk cid pos idx : Z).
Hypothesis HinP : In (pb, pn) (ablocks B lyc Sc). Hypothesis HP0 : pb <= pix. Hypothesis HP1 : pix < pb + pn.
Hypothesis HPF : (pb, pn) <> (flt, nF).
Hypothesis Hfr : In (cid, pos) (frames Sc).
Hypothesis Hpal0 : frame_addr lyc cid pos <= palk. Hypothesis Hpal1 : palk + 766 <= frame_addr lyc cid pos + fs_frame_bytes cid.
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen : 4 * idx + 4 <= nF.
Lemma LDK_seed0 : forall (fy : FPState) (regs : bvmap 5 word) mem md (ix pv cv : Z),
ldk_base fy regs mem md -> getr regs 26 = w64 idx -> getr regs 12 = w64 pix -> getr regs 20 = Z_to_bv 64 (SB + pix / 8) ->
getr regs 27 = w64 palk ->
mbyte trasegs (mrestrict (w_H W) mem) pix = Some (Z_to_bv 8 ix) -> 0 <= ix < 256 ->
mbyte trasegs (mrestrict (w_H W) mem) (palk + 3 * ix) = Some (Z_to_bv 8 pv) -> 0 <= pv < 256 ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * idx) 4 cv -> 0 <= cv < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) [ix; palk + 3 * ix; pv; 0; flt + 4 * idx; cv] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDK_HEAD ldk0_regs (sfr_atoms 64) ldk0_mem None ldk0_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs ldk_Bx ldk0_SH E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
sv_denot E ldk_sh20 = getr regs 20.
Proof.
intros fy regs mem md ix pv cv HB G26 G12 G20 G27 Hixb Hix Hpvb Hpv Vc Hcv E0 E.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pn HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrp].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ pb pn flt nF HAR HinP HinF HPF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds trasegs B LAWS lyc Sc W mem md cid pos HAR Hfr) as (Hfr0 & Hfrc & _).
pose proof (sep_block_frame trasegs B LAWS lyc Sc W mem md pb pn cid pos HAR HinP Hfr) as Hd1. unfold zdisjoint in Hd1. cbn [fst snd] in Hd1.
pose proof (sep_block_frame trasegs B LAWS lyc Sc W mem md flt nF cid pos HAR HinF Hfr) as Hd2. unfold zdisjoint in Hd2. cbn [fst snd] in Hd2.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [ix; palk + 3 * ix; pv; 0; flt + 4 * idx; cv] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U12 : bv_unsigned (ew E0 12) = pix) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - HP0 HP1 Hp4096 Hpceil Hrp C1; lia).
assert (U26 : bv_unsigned (ew E0 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U27 : bv_unsigned (ew E0 27) = palk) by (rewrite (HE0 27%nat 27%bv eq_refl), G27; apply unsigned_lit_small; clear - Hpal0 Hpal1 Hfr0 Hfrc C1; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E0 25) = SB) by (rewrite E25; apply unsigned_lit_small; unfold SB; lia).
assert (A32 : bv_unsigned (ew E0 32) = ix) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hix; lia).
assert (A33 : bv_unsigned (ew E0 33) = palk + 3 * ix) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hix Hpal0 Hpal1 Hfr0 Hfrc C1; lia).
assert (A34 : bv_unsigned (ew E0 34) = pv) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hpv; lia).
assert (A36 : bv_unsigned (ew E0 36) = flt + 4 * idx) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (A37 : bv_unsigned (ew E0 37) = cv) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (ldk_cell4 idx Qf16) as Hf4.
assert (P20 : getr regs 20 = sv_denot E0 ldk_sh20).
{ rewrite G20. symmetry. apply lg_denot_of_U. unfold ldk_sh20. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit. change (Ereg regs _) with E0. rewrite U12, U25, !Z.add_0_r.
rewrite (zcanon_id pix), (zcanon_id SB) by (unfold M64, SB; clear - HP0 HP1 Hp4096 Hpceil Hrp C1; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hq : 0 <= pix / 8 <= pix) by (split; [apply Z.div_pos; clear - HP0 Hp4096; lia | apply Z.div_le_upper_bound; clear - HP0 Hp4096; lia]).
rewrite (zcanon_id (pix / 8)) by (unfold M64; clear - Hq HP0 HP1 Hp4096 Hpceil Hrp C1; lia).
rewrite zcanon_id by (unfold M64, SB; clear - Hq HP0 HP1 Hp4096 Hpceil Hrp C1; lia). lia. }
assert (HS0 : @st_ok trasegs fy E0 ss_LDK0x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDK0x, ldk0_regs. apply (entry_st_ok_full trasegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact P20].
- vm_compute. reflexivity.
- unfold ldk0_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U12.
split; [clear - HP0 Hp4096; lia|]. split; [clear - HP1 Hpceil Hrp C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ pix 0 1 _ ix); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact Hixb | exact Hix].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Hix Hpal0 Hfr0; lia|]. split; [clear - Hix Hpal1 Hfrc C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (palk + 3 * ix) 0 1 _ pv); [exact (DN _ _ A34) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact Hpvb | exact Hpv].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A36.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * idx) 0 4 _ cv); [exact (DN _ _ A37) | zside | zside | rewrite Z.add_0_r; exact Vc].
- apply pairwise_disjoint_of_extents. unfold ldk0_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U12, A33, A36.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - HP0 HP1 Hrp QnF Hidx Hlen Hix Hpal0 Hpal1 Hd Hd1 Hd2. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldk0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U12, U26, U27, U31, E25, A32, A33, A34, A36, A37. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - HP0 HP1 Hp4096 Hpceil Hrp C1 Hidx Hlen Hpal0 Hpal1 Hfr0 Hfrc Qf0 Qf1 Qf16 QnF Hix Hpv Hcv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldk0_facts f_alias alias_ok ldk0_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U26, U31, A36, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id idx) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (idx * 4)) by (unfold M64; clear - Hidx; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, U_SLit, U27, A32, A33, !Z.add_0_r.
rewrite (zcanon_id palk), (zcanon_id ix), (zcanon_id 3) by (unfold M64; clear - Hix Hpal0 Hpal1 Hfr0 Hfrc C1; lia).
rewrite (zcanon_id (ix * 3)) by (unfold M64; clear - Hix; lia). f_equal. lia. }
assert (SHOK0 : sh_ok trasegs ldk_Bx ldk0_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldk0_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 12 pix 1 pix 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pb pn _ _ HAR HinP); clear - HP0 HP1 Hrp; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U12.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pn HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pn HAR HinP) as Himg.
revert Hy Hia Himg HP0 HP1 Hrp Hp4096 Hpceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 36 (flt + 4 * idx) 4 (flt + 4 * idx) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A36.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Himg.
revert Hy Hia Himg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDK0x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldk_Bx ldk0_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|].
rewrite P20. subst E. apply (sv_denot_agree 64 E0 _ _ (env_agree_ew_fregs E0 64 _)). vm_compute. reflexivity.
Qed.
Lemma LDK_S0 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldk_base fy regs mem md -> getr regs 26 = w64 idx -> getr regs 12 = w64 pix -> getr regs 20 = Z_to_bv 64 (SB + pix / 8) ->
getr regs 27 = w64 palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs)) md) (LDK_post fy regs mem LDK_G1 0 0).
Proof.
intros fy regs mem md HB G26 G12 G20 G27.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pn HAR HinP) as (_ & _ & _ & _ & Hppres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrp].
destruct (proj1 (Hppres pix ltac:(clear - HP0 HP1 Hrp; lia))) as (Hhid & bb & Hbb).
assert (Hixb : mbyte trasegs (mrestrict (w_H W) mem) pix = Some (Z_to_bv 8 (bv_unsigned bb))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hbb, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 bb) as Hix. change (bv_modulus 8) with 256 in Hix.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfr) as (_ & _ & Hfpres & _).
destruct (proj1 (Hfpres (palk + 3 * bv_unsigned bb) ltac:(clear - Hix Hpal0 Hpal1; lia))) as (Hhid2 & pp & Hpp).
assert (Hpvb : mbyte trasegs (mrestrict (w_H W) mem) (palk + 3 * bv_unsigned bb) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid2, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hpv. change (bv_modulus 8) with 256 in Hpv.
destruct (ldk_cell_val fy regs mem md idx HB ltac:(lia) Hlen) as (cv & Hcv & Vc).
destruct (LDK_seed0 fy regs mem md _ _ cv HB G26 G12 G20 G27 Hixb Hix Hpvb Hpv Vc Hcv) as (HS & SHOK & HE & HEF & HP20).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HP20.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G1.
{ cbn [ss_mem]. unfold ldk0_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDK_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDK_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [bv_unsigned bb; palk + 3 * bv_unsigned bb; bv_unsigned pp; 0; flt + 4 * idx; cv] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP0 HSL HAE' ltac:(vm_compute; reflexivity)) as HKR0. cbn [ms_regs restrict] in HKR0.
assert (H20 : getr (ms_regs ms) 20 = getr regs 20).
{ rewrite (st_ok_restrict_reg trasegs (w_H W) _ _ ms (20%bv : bv 5) HSL).
lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
fold ldk_sh20. rewrite (sv_denot_agree 96 E _ ldk_sh20 HAEx ltac:(vm_compute; reflexivity)). exact HP20. }
assert (HKR : forall r : bv 5, In r LDK_KEEP -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. destruct (ldk_keep_cases r Hr) as [-> | Hr0]; [exact H20 | exact (HKR0 r Hr0)]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [exact HFK|].
split; [intros a Ha _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(ldk_ro_tac) a Ha) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End S0.
Definition ldku1_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 296 304 0 0 [YQ0b.mkChunk 296 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 38%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 39 0))];
YQ0b.mkRegion None LDK_RO (LDK_RO + 8) 0 0 [YQ0b.mkChunk LDK_RO (CVal 8 (SOff 40 0))] ].
Definition ldku1_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (26%nat, mkAF 0 (2^29) 0); (35%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (38%nat, mkAF 4096 140737479966720 2); (39%nat, mkAF 0 (2^32 - 1) 0) ] []
[ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 26 0) (SLit 2)) (SOff 31 0)) (SAlu ALU_SLL (SOff 35 0) (SLit 2)), SOff 38 0) ].
Definition ss_LDKU1x : sstate := mkSS LDK_U1 sr_atoms ldku1_mem None ldku1_facts.
Definition ldku_SH1 : list shent := [ mkSHE 38 0 4 ].
Section U1.
Variables (idx d s1v : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hd : 0 <= d < 2 ^ 29. Hypothesis Hlen : 4 * (idx + d) + 4 <= nF.
Hypothesis Hs1lo : sp0 - STK <= s1v + 296. Hypothesis Hs1hi : s1v + 304 <= sp0.
Lemma LDK_seedU1 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv rov : Z),
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 9 = w64 s1v -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 d ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (idx + d)) 4 cv -> 0 <= cv < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) LDK_RO 8 rov -> 0 <= rov < 2 ^ 64 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDK_U1 sr_atoms (sfr_atoms 64) ldku1_mem None ldku1_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U1) mem (seg_rom trasegs))) /\
sh_ok trasegs ldk_Bx ldku_SH1 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = flt + 4 * (idx + d).
Proof.
intros fy regs mem md cv rov HB G26 G9 Vslot Vc Hcv Vro Hrov E0 E.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U26 : bv_unsigned (ew E0 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (Rs1 : 2 ^ 46 <= s1v /\ s1v + 304 <= 2 ^ 47 /\ alloc_ceiling <= s1v + 296) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (UD : bv_unsigned (ew E0 35) = d) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hd; lia).
assert (A38 : bv_unsigned (ew E0 38) = flt + 4 * (idx + d)) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (A39 : bv_unsigned (ew E0 39) = cv) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A40 : bv_unsigned (ew E0 40) = rov) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hrov; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (ldk_cell4 (idx + d) Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LDKU1x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U1) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKU1x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldku1_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ s1v 296 8 _ d); [exact (DN _ _ UD) | zside | zside | exact Vslot].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A38.
split; [clear - Qf0 Hidx Hd; lia|]. split; [clear - Qf1 QnF C1 Hidx Hd Hlen; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (flt + 4 * (idx + d) + o) ltac:(clear - Ho Hidx Hd Hlen QnF; lia))). }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (idx + d)) 0 4 _ cv); [exact (DN _ _ A39) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold LDK_RO.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 66448) at 1.
apply (chunk_ok_val trasegs E0 _ 0 66448 8 _ rov); [exact (DN _ _ A40) | zside | zside | exact Vro].
- apply pairwise_disjoint_of_extents. unfold ldku1_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A38. unfold LDK_RO.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hfimg Rs1 Qf0 Qf1 QnF C1 Hidx Hd Hlen. clear. unfold off_img. intros. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldku1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U26, UD, U31, E25, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs1 C1 Hidx Hd Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldku1_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, ?U26, ?UD, ?U31, ?A38, !Z.add_0_r.
change (Z.land (zcanon 2) 63) with 2.
rewrite ?(zcanon_id idx), ?(zcanon_id d), ?(zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite ?(zcanon_id (idx * 4)), ?(zcanon_id (d * 4)) by (unfold M64; clear - Hidx Hd; lia).
rewrite ?(zcanon_id (idx * 4 + flt)), ?(zcanon_id (d * 4 + idx * 4)), ?(zcanon_id (idx * 4 + d * 4)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia). lia. }
assert (SHOK0 : sh_ok trasegs ldk_Bx ldku_SH1 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldku_SH1. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 38 (flt + 4 * (idx + d)) 4 (flt + 4 * (idx + d)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hd Hlen QnF; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A38.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
revert Hy Hia Hfimg Hidx Hd Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDKU1x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldk_Bx ldku_SH1 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LDK_U1_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 9 = w64 s1v -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 d ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_U1) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem LDK_G2 (flt + 4 * (idx + d)) (flt + 4 * (idx + d) + 4)).
Proof.
intros fy regs mem md HB G26 G9 Vslot.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
destruct (ldk_cell_val fy regs mem md (idx + d) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W) mem) LDK_RO (ldk_ro_present (w_H W) mem)) as (rov & Hrov & Vro).
destruct (LDK_seedU1 fy regs mem md cv rov HB G26 G9 Vslot Vc Hcv Vro Hrov) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G2.
{ cbn [ss_mem]. unfold ldku1_mem. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact HU38 | | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hidx Hd Hlen QnF; lia]. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDK_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDK_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [exact HFK|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 38%nat (flt + 4 * (idx + d)) 0 4 HFr); [ldk_rs_tac | exact HU38 | exact Ha | clear - Hnw; lia].
Qed.
End U1.
Definition ldku2_mem : smem :=
[ YQ0b.mkRegion (Some 38%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 39 0))];
YQ0b.mkRegion None LDK_RO (LDK_RO + 8) 0 0 [YQ0b.mkChunk LDK_RO (CVal 8 (SOff 40 0))] ].
Definition ldku2_facts : facts :=
mkFacts [ (26%nat, mkAF 0 (2^29) 0); (17%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (38%nat, mkAF 4096 140737479966720 2); (39%nat, mkAF 0 (2^32 - 1) 0) ] []
[ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 17 0) (SLit 2)) (SAlu ALU_SLL (SOff 26 0) (SLit 2))) (SOff 31 0), SOff 38 0) ].
Definition ss_LDKU2x : sstate := mkSS LDK_U2 sr_atoms ldku2_mem None ldku2_facts.
Definition ldku_SH2 : list shent := [ mkSHE 38 0 4 ].
Section U2.
Variables (idx d  : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hd : 0 <= d < 2 ^ 29. Hypothesis Hlen : 4 * (idx + d) + 4 <= nF.
Lemma LDK_seedU2 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv rov : Z),
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 17 = w64 d ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (idx + d)) 4 cv -> 0 <= cv < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) LDK_RO 8 rov -> 0 <= rov < 2 ^ 64 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDK_U2 sr_atoms (sfr_atoms 64) ldku2_mem None ldku2_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U2) mem (seg_rom trasegs))) /\
sh_ok trasegs ldk_Bx ldku_SH2 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = flt + 4 * (idx + d).
Proof.
intros fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov E0 E.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U26 : bv_unsigned (ew E0 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (UD : bv_unsigned (ew E0 17) = d) by (rewrite (HE0 17%nat 17%bv eq_refl), GD; apply unsigned_lit_small; clear - Hd; lia).
assert (A38 : bv_unsigned (ew E0 38) = flt + 4 * (idx + d)) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (A39 : bv_unsigned (ew E0 39) = cv) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A40 : bv_unsigned (ew E0 40) = rov) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hrov; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (ldk_cell4 (idx + d) Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LDKU2x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U2) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKU2x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldku2_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A38.
split; [clear - Qf0 Hidx Hd; lia|]. split; [clear - Qf1 QnF C1 Hidx Hd Hlen; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (flt + 4 * (idx + d) + o) ltac:(clear - Ho Hidx Hd Hlen QnF; lia))). }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (idx + d)) 0 4 _ cv); [exact (DN _ _ A39) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold LDK_RO.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 66448) at 1.
apply (chunk_ok_val trasegs E0 _ 0 66448 8 _ rov); [exact (DN _ _ A40) | zside | zside | exact Vro].
- apply pairwise_disjoint_of_extents. unfold ldku2_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A38. unfold LDK_RO.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hfimg Qf0 Qf1 QnF C1 Hidx Hd Hlen. clear. unfold off_img. intros. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldku2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U26, UD, U31, E25, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - C1 Hidx Hd Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldku2_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, ?U26, ?UD, ?U31, ?A38, !Z.add_0_r.
change (Z.land (zcanon 2) 63) with 2.
rewrite ?(zcanon_id idx), ?(zcanon_id d), ?(zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite ?(zcanon_id (idx * 4)), ?(zcanon_id (d * 4)) by (unfold M64; clear - Hidx Hd; lia).
rewrite ?(zcanon_id (idx * 4 + flt)), ?(zcanon_id (d * 4 + idx * 4)), ?(zcanon_id (idx * 4 + d * 4)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia). lia. }
assert (SHOK0 : sh_ok trasegs ldk_Bx ldku_SH2 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldku_SH2. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 38 (flt + 4 * (idx + d)) 4 (flt + 4 * (idx + d)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hd Hlen QnF; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A38.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
revert Hy Hia Hfimg Hidx Hd Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDKU2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldk_Bx ldku_SH2 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LDK_U2_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 17 = w64 d ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_U2) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem LDK_G3 (flt + 4 * (idx + d)) (flt + 4 * (idx + d) + 4)).
Proof.
intros fy regs mem md HB G26 GD.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
destruct (ldk_cell_val fy regs mem md (idx + d) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W) mem) LDK_RO (ldk_ro_present (w_H W) mem)) as (rov & Hrov & Vro).
destruct (LDK_seedU2 fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G3.
{ cbn [ss_mem]. unfold ldku2_mem.
eapply awr_ok_cons_gen; [reflexivity | exact HU38 | | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hidx Hd Hlen QnF; lia]. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDK_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDK_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [exact HFK|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 38%nat (flt + 4 * (idx + d)) 0 4 HFr); [ldk_rs_tac | exact HU38 | exact Ha | clear - Hnw; lia].
Qed.
End U2.
Definition ldku3_mem : smem :=
[ YQ0b.mkRegion (Some 38%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 39 0))];
YQ0b.mkRegion None LDK_RO (LDK_RO + 8) 0 0 [YQ0b.mkChunk LDK_RO (CVal 8 (SOff 40 0))] ].
Definition ldku3_facts : facts :=
mkFacts [ (26%nat, mkAF 0 (2^29) 0); (29%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (38%nat, mkAF 4096 140737479966720 2); (39%nat, mkAF 0 (2^32 - 1) 0) ] []
[ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 26 0) (SLit 2)) (SAlu ALU_SLL (SOff 29 0) (SLit 2))) (SOff 31 0), SOff 38 0) ].
Definition ss_LDKU3x : sstate := mkSS LDK_U3 sr_atoms ldku3_mem None ldku3_facts.
Definition ldku_SH3 : list shent := [ mkSHE 38 0 4 ].
Section U3.
Variables (idx d  : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hd : 0 <= d < 2 ^ 29. Hypothesis Hlen : 4 * (idx + d) + 4 <= nF.
Lemma LDK_seedU3 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv rov : Z),
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 29 = w64 d ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (idx + d)) 4 cv -> 0 <= cv < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) LDK_RO 8 rov -> 0 <= rov < 2 ^ 64 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDK_U3 sr_atoms (sfr_atoms 64) ldku3_mem None ldku3_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U3) mem (seg_rom trasegs))) /\
sh_ok trasegs ldk_Bx ldku_SH3 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = flt + 4 * (idx + d).
Proof.
intros fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov E0 E.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U26 : bv_unsigned (ew E0 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (UD : bv_unsigned (ew E0 29) = d) by (rewrite (HE0 29%nat 29%bv eq_refl), GD; apply unsigned_lit_small; clear - Hd; lia).
assert (A38 : bv_unsigned (ew E0 38) = flt + 4 * (idx + d)) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (A39 : bv_unsigned (ew E0 39) = cv) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A40 : bv_unsigned (ew E0 40) = rov) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hrov; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (ldk_cell4 (idx + d) Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LDKU3x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U3) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKU3x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldku3_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A38.
split; [clear - Qf0 Hidx Hd; lia|]. split; [clear - Qf1 QnF C1 Hidx Hd Hlen; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (flt + 4 * (idx + d) + o) ltac:(clear - Ho Hidx Hd Hlen QnF; lia))). }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (idx + d)) 0 4 _ cv); [exact (DN _ _ A39) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold LDK_RO.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 66448) at 1.
apply (chunk_ok_val trasegs E0 _ 0 66448 8 _ rov); [exact (DN _ _ A40) | zside | zside | exact Vro].
- apply pairwise_disjoint_of_extents. unfold ldku3_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A38. unfold LDK_RO.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hfimg Qf0 Qf1 QnF C1 Hidx Hd Hlen. clear. unfold off_img. intros. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldku3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U26, UD, U31, E25, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - C1 Hidx Hd Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldku3_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, ?U26, ?UD, ?U31, ?A38, !Z.add_0_r.
change (Z.land (zcanon 2) 63) with 2.
rewrite ?(zcanon_id idx), ?(zcanon_id d), ?(zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite ?(zcanon_id (idx * 4)), ?(zcanon_id (d * 4)) by (unfold M64; clear - Hidx Hd; lia).
rewrite ?(zcanon_id (idx * 4 + flt)), ?(zcanon_id (d * 4 + idx * 4)), ?(zcanon_id (idx * 4 + d * 4)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia). lia. }
assert (SHOK0 : sh_ok trasegs ldk_Bx ldku_SH3 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldku_SH3. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 38 (flt + 4 * (idx + d)) 4 (flt + 4 * (idx + d)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hd Hlen QnF; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A38.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
revert Hy Hia Hfimg Hidx Hd Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDKU3x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldk_Bx ldku_SH3 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LDK_U3_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 29 = w64 d ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_U3) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem LDK_G4 (flt + 4 * (idx + d)) (flt + 4 * (idx + d) + 4)).
Proof.
intros fy regs mem md HB G26 GD.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
destruct (ldk_cell_val fy regs mem md (idx + d) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W) mem) LDK_RO (ldk_ro_present (w_H W) mem)) as (rov & Hrov & Vro).
destruct (LDK_seedU3 fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G4.
{ cbn [ss_mem]. unfold ldku3_mem.
eapply awr_ok_cons_gen; [reflexivity | exact HU38 | | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hidx Hd Hlen QnF; lia]. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDK_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDK_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [exact HFK|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 38%nat (flt + 4 * (idx + d)) 0 4 HFr); [ldk_rs_tac | exact HU38 | exact Ha | clear - Hnw; lia].
Qed.
End U3.
Definition ldku4_mem : smem :=
[ YQ0b.mkRegion (Some 38%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 39 0))];
YQ0b.mkRegion None LDK_RO (LDK_RO + 8) 0 0 [YQ0b.mkChunk LDK_RO (CVal 8 (SOff 40 0))] ].
Definition ldku4_facts : facts :=
mkFacts [ (26%nat, mkAF 0 (2^29) 0); (28%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (38%nat, mkAF 4096 140737479966720 2); (39%nat, mkAF 0 (2^32 - 1) 0) ] []
[ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 26 0) (SLit 2)) (SAlu ALU_SLL (SOff 28 0) (SLit 2))) (SOff 31 0), SOff 38 0) ].
Definition ss_LDKU4x : sstate := mkSS LDK_U4 sr_atoms ldku4_mem None ldku4_facts.
Definition ldku_SH4 : list shent := [ mkSHE 38 0 4 ].
Section U4.
Variables (idx d  : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hd : 0 <= d < 2 ^ 29. Hypothesis Hlen : 4 * (idx + d) + 4 <= nF.
Lemma LDK_seedU4 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv rov : Z),
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 28 = w64 d ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (idx + d)) 4 cv -> 0 <= cv < 2 ^ 32 ->
val_mem trasegs (mrestrict (w_H W) mem) LDK_RO 8 rov -> 0 <= rov < 2 ^ 64 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDK_U4 sr_atoms (sfr_atoms 64) ldku4_mem None ldku4_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U4) mem (seg_rom trasegs))) /\
sh_ok trasegs ldk_Bx ldku_SH4 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = flt + 4 * (idx + d).
Proof.
intros fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov E0 E.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U26 : bv_unsigned (ew E0 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (UD : bv_unsigned (ew E0 28) = d) by (rewrite (HE0 28%nat 28%bv eq_refl), GD; apply unsigned_lit_small; clear - Hd; lia).
assert (A38 : bv_unsigned (ew E0 38) = flt + 4 * (idx + d)) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
assert (A39 : bv_unsigned (ew E0 39) = cv) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A40 : bv_unsigned (ew E0 40) = rov) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hrov; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (ldk_cell4 (idx + d) Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LDKU4x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_U4) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKU4x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldku4_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A38.
split; [clear - Qf0 Hidx Hd; lia|]. split; [clear - Qf1 QnF C1 Hidx Hd Hlen; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (flt + 4 * (idx + d) + o) ltac:(clear - Ho Hidx Hd Hlen QnF; lia))). }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (idx + d)) 0 4 _ cv); [exact (DN _ _ A39) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold LDK_RO.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 66448) at 1.
apply (chunk_ok_val trasegs E0 _ 0 66448 8 _ rov); [exact (DN _ _ A40) | zside | zside | exact Vro].
- apply pairwise_disjoint_of_extents. unfold ldku4_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A38. unfold LDK_RO.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hfimg Qf0 Qf1 QnF C1 Hidx Hd Hlen. clear. unfold off_img. intros. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldku4_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U26, UD, U31, E25, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - C1 Hidx Hd Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldku4_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, ?U26, ?UD, ?U31, ?A38, !Z.add_0_r.
change (Z.land (zcanon 2) 63) with 2.
rewrite ?(zcanon_id idx), ?(zcanon_id d), ?(zcanon_id flt) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite ?(zcanon_id (idx * 4)), ?(zcanon_id (d * 4)) by (unfold M64; clear - Hidx Hd; lia).
rewrite ?(zcanon_id (idx * 4 + flt)), ?(zcanon_id (d * 4 + idx * 4)), ?(zcanon_id (idx * 4 + d * 4)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hd Hlen; lia). lia. }
assert (SHOK0 : sh_ok trasegs ldk_Bx ldku_SH4 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldku_SH4. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 ldk_Bx 38 (flt + 4 * (idx + d)) 4 (flt + 4 * (idx + d)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hd Hlen QnF; lia.
+ unfold U, ldk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A38.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
revert Hy Hia Hfimg Hidx Hd Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDKU4x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldk_Bx ldku_SH4 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LDK_U4_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldk_base fy regs mem md -> getr regs 26 = w64 idx ->
getr regs 28 = w64 d ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_U4) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem LDK_S5 (flt + 4 * (idx + d)) (flt + 4 * (idx + d) + 4)).
Proof.
intros fy regs mem md HB G26 GD.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & Hfrm & G31 & G25).
destruct (ldk_cell_val fy regs mem md (idx + d) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (val_mem_of_present8 trasegs (mrestrict (w_H W) mem) LDK_RO (ldk_ro_present (w_H W) mem)) as (rov & Hrov & Vro).
destruct (LDK_seedU4 fy regs mem md cv rov HB G26 GD Vc Hcv Vro Hrov) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_S5.
{ cbn [ss_mem]. unfold ldku4_mem.
eapply awr_ok_cons_gen; [reflexivity | exact HU38 | | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (flt + (a - flt)) by lia. apply HFW; [exact HinF | clear - Ha Hidx Hd Hlen QnF; lia]. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDK_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDK_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; d; 0; 0; flt + 4 * (idx + d); cv; rov] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [exact HFK|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 38%nat (flt + 4 * (idx + d)) 0 4 HFr); [ldk_rs_tac | exact HU38 | exact Ha | clear - Hnw; lia].
Qed.
End U4.
Definition ss_LDKG1 : sstate := mkSS LDK_G1 sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDK_guard1 : forall (fy : FPState) (regs : bvmap 5 word) mem md (a b : Z),
ldk_base fy regs mem md -> getr regs 23 = w64 a -> 0 <= a < 2 ^ 64 ->
getr regs 15 = w64 b -> 0 <= b < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G1) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem (if b <=? a then LDK_G2 else LDK_U1) 0 0).
Proof.
intros fy regs mem md a b HB GA Ha GB Hb.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (UA : bv_unsigned (ew E 23) = a) by (rewrite (HE0 23%nat 23%bv eq_refl), GA; apply unsigned_lit_small; exact Ha).
assert (UB : bv_unsigned (ew E 15) = b) by (rewrite (HE0 15%nat 15%bv eq_refl), GB; apply unsigned_lit_small; exact Hb).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDKG1 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_G1) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKG1. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldk_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDK_G1) mem (seg_rom trasegs))) in HJ, SHOK.
srr_branch_tok tratbl_lib_ok HS SHOK ldk_Bspan.
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_true_iff, Z.ltb_ge in Hc. replace (b <=? a) with true by (symmetry; apply Z.leb_le; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G2. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc. replace (b <=? a) with false by (symmetry; apply Z.leb_gt; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_U1. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ss_LDKG2 : sstate := mkSS LDK_G2 sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDK_guard2 : forall (fy : FPState) (regs : bvmap 5 word) mem md (a b : Z),
ldk_base fy regs mem md -> getr regs 16 = w64 a -> 0 <= a < 2 ^ 64 ->
getr regs 30 = w64 b -> 0 <= b < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G2) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem (if b <=? a then LDK_S5 else LDK_U2) 0 0).
Proof.
intros fy regs mem md a b HB GA Ha GB Hb.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (UA : bv_unsigned (ew E 16) = a) by (rewrite (HE0 16%nat 16%bv eq_refl), GA; apply unsigned_lit_small; exact Ha).
assert (UB : bv_unsigned (ew E 30) = b) by (rewrite (HE0 30%nat 30%bv eq_refl), GB; apply unsigned_lit_small; exact Hb).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDKG2 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_G2) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKG2. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldk_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDK_G2) mem (seg_rom trasegs))) in HJ, SHOK.
srr_branch_tok tratbl_lib_ok HS SHOK ldk_Bspan.
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_true_iff, Z.ltb_ge in Hc. replace (b <=? a) with true by (symmetry; apply Z.leb_le; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_S5. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc. replace (b <=? a) with false by (symmetry; apply Z.leb_gt; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_U2. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ss_LDKG3 : sstate := mkSS LDK_G3 sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDK_guard3 : forall (fy : FPState) (regs : bvmap 5 word) mem md (a  : Z),
ldk_base fy regs mem md -> getr regs 23 = w64 a -> 0 <= a < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G3) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem (if a =? 0 then LDK_G4 else LDK_U3) 0 0).
Proof.
intros fy regs mem md a  HB GA Ha .
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (UA : bv_unsigned (ew E 23) = a) by (rewrite (HE0 23%nat 23%bv eq_refl), GA; apply unsigned_lit_small; exact Ha).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDKG3 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_G3) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKG3. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldk_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDK_G3) mem (seg_rom trasegs))) in HJ, SHOK.
srr_branch_tok tratbl_lib_ok HS SHOK ldk_Bspan.
- rewrite branch_eq_U, U_SOff, U_SLit, UA, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_G4. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
- rewrite branch_eq_U, U_SOff, U_SLit, UA, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_U3. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ss_LDKG4 : sstate := mkSS LDK_G4 sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDK_guard4 : forall (fy : FPState) (regs : bvmap 5 word) mem md (a b : Z),
ldk_base fy regs mem md -> getr regs 23 = w64 a -> 0 <= a < 2 ^ 64 ->
getr regs 15 = w64 b -> 0 <= b < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G4) mem (seg_rom trasegs)) md)
(LDK_post fy regs mem (if b <=? a then LDK_S5 else LDK_U4) 0 0).
Proof.
intros fy regs mem md a b HB GA Ha GB Hb.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (UA : bv_unsigned (ew E 23) = a) by (rewrite (HE0 23%nat 23%bv eq_refl), GA; apply unsigned_lit_small; exact Ha).
assert (UB : bv_unsigned (ew E 15) = b) by (rewrite (HE0 15%nat 15%bv eq_refl), GB; apply unsigned_lit_small; exact Hb).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDKG4 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_G4) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDKG4. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldk_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDK_G4) mem (seg_rom trasegs))) in HJ, SHOK.
srr_branch_tok tratbl_lib_ok HS SHOK ldk_Bspan.
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_true_iff, Z.ltb_ge in Hc. replace (b <=? a) with true by (symmetry; apply Z.leb_le; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_S5. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
- rewrite branch_geu_U, !U_SOff, UA, UB, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc. replace (b <=? a) with false by (symmetry; apply Z.leb_gt; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_U4. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDK_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ss_LDK5 : sstate := mkSS LDK_S5 sr_atoms [] None (mkFacts [ (24%nat, mkAF 1 3 0); (25%nat, mkAF SB SB 0) ] [] []).
Definition LDK_tpost (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (c idx palk : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if c =? 1 then LDK_EXIT else LDK_HEAD)) mem' (seg_rom trasegs)) md' /\
ldk_base fy' regs' mem' md' /\
getr regs' 24 = w64 (c - 1) /\ getr regs' 26 = w64 (idx + 1) /\ getr regs' 27 = w64 (palk + 1) /\
(forall r : bv 5, In r LDK_KEEPL -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDK_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDK_S5_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (c idx palk : Z),
ldk_base fy regs mem md -> getr regs 24 = w64 c -> getr regs 26 = w64 idx -> getr regs 27 = w64 palk ->
1 <= c <= 3 -> 0 <= idx < 2 ^ 62 -> 0 <= palk < 2 ^ 62 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_S5) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md c idx palk HB G24 G26 G27 Hc Hidx Hpalk.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U24 : bv_unsigned (ew E 24) = c) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = idx) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = palk) by (rewrite (HE0 27%nat 27%bv eq_refl), G27; apply unsigned_lit_small; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDK5 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDK_S5) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDK5. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U24, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldk_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDK_S5) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_BR. { apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 E Ex) by (env_agree_chain HAE) end.
assert (FIN : forall E' ss' ms' md', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 32 E E' ->
ss_pc ss' = (if c =? 1 then LDK_EXIT else LDK_HEAD) -> ss_resv ss' = None ->
sr_get (ss_regs ss') 24 = SOff 24 (-1) -> sr_get (ss_regs ss') 26 = SOff 26 1 -> sr_get (ss_regs ss') 27 = SOff 27 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LDK_KEEPL = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LDK_tpost fy regs mem c idx palk)).
{ intros E' ss' ms' md' HS' [EA ED] Hpc' Hrv' Q24 Q26 Q27 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs []) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LDK_KEEPL HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (24%bv : bv 5) HS'), Q24; cbn [sv_denot]; rewrite EA, U24 by lia; unfold w64; f_equal; lia|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (26%bv : bv 5) HS'), Q26; cbn [sv_denot]; rewrite EA, U26 by lia; reflexivity|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (27%bv : bv 5) HS'), Q27; cbn [sv_denot]; rewrite EA, U27 by lia; reflexivity|].
split; [exact HKR|]. split; [intros r Hr; reflexivity|].
split; [intros a Ha _; exact (Hk' a Ha) | exact Hp']. }
srr_branch_tok tratbl_lib_ok HS SHOK ldk_Bspan.
- rewrite branch_ne_U, U_SOff, U_SLit in Hc0. rewrite ?(proj1 HAEx) in Hc0 by lia. rewrite U24, !zcanon_id in Hc0 by (unfold M64; lia).
apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
assert (Ec : (c =? 1) = false) by (apply Z.eqb_neq; lia).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_HEAD. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ HS HAEy); [rewrite Ec; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
- rewrite branch_ne_U, U_SOff, U_SLit in Hc0. rewrite ?(proj1 HAEx) in Hc0 by lia. rewrite U24, !zcanon_id in Hc0 by (unfold M64; lia).
apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
assert (Ec : (c =? 1) = true) by (apply Z.eqb_eq; lia).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldk_Bspan LDK_EXIT. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ HS HAEy); [rewrite Ec; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
Qed.
Section f.
Variables (pb pn pix cid pos s1v d1 d2 d3 d4 g15 g16 g23 g30 : Z).
Hypothesis HinP : In (pb, pn) (ablocks B lyc Sc). Hypothesis HP0 : pb <= pix. Hypothesis HP1 : pix < pb + pn.
Hypothesis HPF : (pb, pn) <> (flt, nF).
Hypothesis Hfr : In (cid, pos) (frames Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v + 296. Hypothesis Hs1hi : s1v + 304 <= sp0.
Hypothesis Hd1 : 0 <= d1 < 2 ^ 29. Hypothesis Hd2 : 0 <= d2 < 2 ^ 29. Hypothesis Hd3 : 0 <= d3 < 2 ^ 29. Hypothesis Hd4 : 0 <= d4 < 2 ^ 29.
Hypothesis Hg15 : 0 <= g15 < 2 ^ 64. Hypothesis Hg16 : 0 <= g16 < 2 ^ 64. Hypothesis Hg23 : 0 <= g23 < 2 ^ 64. Hypothesis Hg30 : 0 <= g30 < 2 ^ 64.
Definition ldk_regs (regs : bvmap 5 word) : Prop :=
getr regs 9 = w64 s1v /\ getr regs 12 = w64 pix /\ getr regs 20 = Z_to_bv 64 (SB + pix / 8) /\
getr regs 15 = w64 g15 /\ getr regs 16 = w64 g16 /\ getr regs 23 = w64 g23 /\ getr regs 30 = w64 g30 /\
getr regs 17 = w64 d2 /\ getr regs 29 = w64 d3 /\ getr regs 28 = w64 d4.
Definition ldk_sinv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (c idx palk : Z) : Prop :=
ldk_base fy regs mem md /\ ldk_regs regs /\ getr regs 24 = w64 c /\ getr regs 26 = w64 idx /\ getr regs 27 = w64 palk /\
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 d1.
Lemma ldk_regs_kept : forall regs regs' : bvmap 5 word, (forall r : bv 5, In r LDK_KEEPL -> getr regs' r = getr regs r) -> ldk_regs regs -> ldk_regs regs'.
Proof.
intros regs regs' HK (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28). unfold ldk_regs.
rewrite (HK (9%bv : bv 5) ltac:(cbv; tauto)), (HK (12%bv : bv 5) ltac:(cbv; tauto)), (HK (20%bv : bv 5) ltac:(cbv; tauto)),
(HK (15%bv : bv 5) ltac:(cbv; tauto)), (HK (16%bv : bv 5) ltac:(cbv; tauto)), (HK (23%bv : bv 5) ltac:(cbv; tauto)),
(HK (30%bv : bv 5) ltac:(cbv; tauto)), (HK (17%bv : bv 5) ltac:(cbv; tauto)), (HK (29%bv : bv 5) ltac:(cbv; tauto)),
(HK (28%bv : bv 5) ltac:(cbv; tauto)).
repeat split; assumption.
Qed.
Lemma ldk_slot_kept : forall fy regs mem md (mem' : word -> option byte),
ldk_base fy regs mem md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 d1 -> val_mem trasegs (mrestrict (w_H W) mem') (s1v + 296) 8 d1.
Proof.
intros fy regs mem md mem' HB Hm V. pose proof (ldk_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HB as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Rs1 : 2 ^ 46 <= s1v /\ s1v + 304 <= 2 ^ 47 /\ alloc_ceiling <= s1v + 296) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
apply (YC04.val_mem_kept trasegs (w_H W) (w_H W) mem mem' (s1v + 296) 8 d1); [|exact V].
intros j Hj. apply Hm; [clear - Hj Rs1; lia | clear - Hj Rs1 Qf1 QnF; lia].
Qed.
Lemma ldk_tpost_trans : forall fy regs mem fy1 regs1 mem1 c idx palk W' c',
(forall r : bv 5, In r LDK_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LDK_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
LDK_tpost fy1 regs1 mem1 c idx palk W' c' -> LDK_tpost fy regs mem c idx palk W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 c idx palk W' c' HK1 HF1 HM1 HX1 (HW & fy' & regs' & mem' & md' & Hc & HB' & R24 & R26 & R27 & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HB'|]. split; [exact R24|]. split; [exact R26|]. split; [exact R27|].
split; [intros r Hr; rewrite (HK r Hr); apply HK1; apply ldk_keepl_keep; exact Hr|].
split; [intros r Hr; rewrite (HF r Hr); apply HF1; exact Hr|].
split; [intros a Ha Hn; rewrite (HM a Ha Hn); apply HM1; assumption|].
intros a Ha. apply HX. apply HX1. exact Ha.
Qed.
Lemma ldk_chain : forall fy regs mem md c idx palk pc lo hi cfg0,
ldk_sinv fy regs mem md c idx palk -> (lo = hi \/ (flt <= lo /\ hi <= flt + nF)) ->
SRr trasegs W cfg0 (LDK_post fy regs mem pc lo hi) ->
(forall (fy1 : FPState) regs1 mem1 md1, ldk_sinv fy1 regs1 mem1 md1 c idx palk ->
SRr trasegs W (mkCfg (@mkst fy1 regs1 (Z_to_bv 64 pc) mem1 (seg_rom trasegs)) md1) (LDK_tpost fy1 regs1 mem1 c idx palk)) ->
SRr trasegs W cfg0 (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md c idx palk pc lo hi cfg0 (HB & HR & R24 & R26 & R27 & Vs) Hlh Hstep Hcont.
eapply SRr_bind; [exact Hstep|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & HB1 & HK1 & HF1 & HM1 & HX1).
assert (HMc : forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply HM1; [exact Ha|]. destruct Hlh as [-> | [Hl Hh]]; lia. }
eapply SRr_mono.
{ apply Hcont. split; [exact HB1|].
split; [exact (ldk_regs_kept regs regs1 (fun r Hr => HK1 r (ldk_keepl_keep r Hr)) HR)|].
split; [rewrite (HK1 (24%bv : bv 5) ltac:(cbv; tauto)); exact R24|].
split; [rewrite (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact R26|].
split; [rewrite (HK1 (27%bv : bv 5) ltac:(cbv; tauto)); exact R27|].
exact (ldk_slot_kept fy regs mem md mem1 HB HMc Vs). }
intros W'' c'' _ H. exact (ldk_tpost_trans fy regs mem fy1 regs1 mem1 c idx palk W'' c'' HK1 HF1 HMc HX1 H).
Qed.
Section g.
Variables (c idx palk : Z).
Hypothesis Hc : 1 <= c <= 3. Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen0 : 4 * idx + 4 <= nF.
Hypothesis Hpal0 : frame_addr lyc cid pos <= palk. Hypothesis Hpal1 : palk + 766 <= frame_addr lyc cid pos + fs_frame_bytes cid.
Hypothesis HB1 : g23 < g15 -> 4 * (idx + d1) + 4 <= nF.
Hypothesis HB2 : g16 < g30 -> 4 * (idx + d2) + 4 <= nF.
Hypothesis HB3 : g16 < g30 -> g23 <> 0 -> 4 * (idx + d3) + 4 <= nF.
Hypothesis HB4 : g16 < g30 -> g23 < g15 -> 4 * (idx + d4) + 4 <= nF.
Lemma LDK_K5 : forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_S5) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md (HB & HR & R24 & R26 & R27 & Vs).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (frames_bounds trasegs B LAWS lyc Sc W mem md cid pos HAR Hfr) as (Hfr0 & Hfrc & _).
apply (LDK_S5_run fy regs mem md c idx palk HB R24 R26 R27 Hc); [clear - Hidx; lia | clear - Hpal0 Hpal1 Hfr0 Hfrc C1; lia].
Qed.
Lemma LDK_K4 : g16 < g30 -> forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G4) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros Hg2 fy regs mem md HI. pose proof HI as (HB & (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28) & R24 & R26 & R27 & Vs).
apply (ldk_chain fy regs mem md c idx palk _ 0 0 _ HI ltac:(left; reflexivity) (LDK_guard4 fy regs mem md g23 g15 HB R23 Hg23 R15 Hg15)).
intros fy1 regs1 mem1 md1 HI1. destruct (g15 <=? g23) eqn:Eg; [exact (LDK_K5 fy1 regs1 mem1 md1 HI1)|]. apply Z.leb_gt in Eg.
pose proof HI1 as (HB1' & (_ & _ & _ & _ & _ & _ & _ & _ & _ & R28') & _ & R26' & _ & _).
apply (ldk_chain fy1 regs1 mem1 md1 c idx palk _ (flt + 4 * (idx + d4)) (flt + 4 * (idx + d4) + 4) _ HI1 ltac:(right; pose proof (HB4 Hg2 Eg); clear - Hidx Hd4 H; lia)
(LDK_U4_run idx d4 Hidx Hd4 (HB4 Hg2 Eg) fy1 regs1 mem1 md1 HB1' R26' R28')).
exact LDK_K5.
Qed.
Lemma LDK_K3 : g16 < g30 -> forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G3) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros Hg2 fy regs mem md HI. pose proof HI as (HB & (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28) & R24 & R26 & R27 & Vs).
apply (ldk_chain fy regs mem md c idx palk _ 0 0 _ HI ltac:(left; reflexivity) (LDK_guard3 fy regs mem md g23 HB R23 Hg23)).
intros fy1 regs1 mem1 md1 HI1. destruct (g23 =? 0) eqn:Eg; [exact (LDK_K4 Hg2 fy1 regs1 mem1 md1 HI1)|]. apply Z.eqb_neq in Eg.
pose proof HI1 as (HB1' & (_ & _ & _ & _ & _ & _ & _ & _ & R29' & _) & _ & R26' & _ & _).
apply (ldk_chain fy1 regs1 mem1 md1 c idx palk _ (flt + 4 * (idx + d3)) (flt + 4 * (idx + d3) + 4) _ HI1 ltac:(right; pose proof (HB3 Hg2 Eg); clear - Hidx Hd3 H; lia)
(LDK_U3_run idx d3 Hidx Hd3 (HB3 Hg2 Eg) fy1 regs1 mem1 md1 HB1' R26' R29')).
exact (LDK_K4 Hg2).
Qed.
Lemma LDK_K2 : forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G2) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md HI. pose proof HI as (HB & (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28) & R24 & R26 & R27 & Vs).
apply (ldk_chain fy regs mem md c idx palk _ 0 0 _ HI ltac:(left; reflexivity) (LDK_guard2 fy regs mem md g16 g30 HB R16 Hg16 R30 Hg30)).
intros fy1 regs1 mem1 md1 HI1. destruct (g30 <=? g16) eqn:Eg; [exact (LDK_K5 fy1 regs1 mem1 md1 HI1)|]. apply Z.leb_gt in Eg.
pose proof HI1 as (HB1' & (_ & _ & _ & _ & _ & _ & _ & R17' & _ & _) & _ & R26' & _ & _).
apply (ldk_chain fy1 regs1 mem1 md1 c idx palk _ (flt + 4 * (idx + d2)) (flt + 4 * (idx + d2) + 4) _ HI1 ltac:(right; pose proof (HB2 Eg); clear - Hidx Hd2 H; lia)
(LDK_U2_run idx d2 Hidx Hd2 (HB2 Eg) fy1 regs1 mem1 md1 HB1' R26' R17')).
exact (LDK_K3 Eg).
Qed.
Lemma LDK_K1 : forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_G1) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md HI. pose proof HI as (HB & (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28) & R24 & R26 & R27 & Vs).
apply (ldk_chain fy regs mem md c idx palk _ 0 0 _ HI ltac:(left; reflexivity) (LDK_guard1 fy regs mem md g23 g15 HB R23 Hg23 R15 Hg15)).
intros fy1 regs1 mem1 md1 HI1. destruct (g15 <=? g23) eqn:Eg; [exact (LDK_K2 fy1 regs1 mem1 md1 HI1)|]. apply Z.leb_gt in Eg.
pose proof HI1 as (HB1' & (R9' & _) & _ & R26' & _ & Vs').
apply (ldk_chain fy1 regs1 mem1 md1 c idx palk _ (flt + 4 * (idx + d1)) (flt + 4 * (idx + d1) + 4) _ HI1 ltac:(right; pose proof (HB1 Eg); clear - Hidx Hd1 H; lia)
(LDK_U1_run idx d1 s1v Hidx Hd1 (HB1 Eg) Hs1lo Hs1hi fy1 regs1 mem1 md1 HB1' R26' R9' Vs')).
exact LDK_K2.
Qed.
Lemma LDK_trip : forall (fy : FPState) regs mem md, ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs)) md) (LDK_tpost fy regs mem c idx palk).
Proof.
intros fy regs mem md HI. pose proof HI as (HB & (R9 & R12 & R20 & R15 & R16 & R23 & R30 & R17 & R29 & R28) & R24 & R26 & R27 & Vs).
apply (ldk_chain fy regs mem md c idx palk _ 0 0 _ HI ltac:(left; reflexivity)
(LDK_S0 pb pn pix palk cid pos idx HinP HP0 HP1 HPF Hfr Hpal0 Hpal1 Hidx Hlen0 fy regs mem md HB R26 R12 R20 R27)).
exact LDK_K1.
Qed.
End g.
Definition LDK_lpost (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (c idx palk : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LDK_EXIT) mem' (seg_rom trasegs)) md' /\
ldk_base fy' regs' mem' md' /\
getr regs' 24 = w64 0 /\ getr regs' 26 = w64 (idx + c) /\ getr regs' 27 = w64 (palk + c) /\
(forall r : bv 5, In r LDK_KEEPL -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDK_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDK_loop : forall (n : nat) (fy : FPState) regs mem md (c idx palk : Z),
Z.of_nat n = c - 1 -> 1 <= c <= 3 -> 0 <= idx -> idx + c <= 2 ^ 29 ->
frame_addr lyc cid pos <= palk -> palk + (c - 1) + 766 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall j, 0 <= j < c -> 4 * (idx + j) + 4 <= nF) ->
(forall j, 0 <= j < c -> g23 < g15 -> 4 * (idx + j + d1) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> 4 * (idx + j + d2) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> g23 <> 0 -> 4 * (idx + j + d3) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> g23 < g15 -> 4 * (idx + j + d4) + 4 <= nF) ->
ldk_sinv fy regs mem md c idx palk ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) mem (seg_rom trasegs)) md) (LDK_lpost fy regs mem c idx palk).
Proof.
induction n as [|n IH]; intros fy regs mem md c idx palk Hn Hc Hidx Hmax Hpal0 Hpal1 HL0 HL1 HL2 HL3 HL4 HI.
all: assert (T0 : 4 * idx + 4 <= nF) by (pose proof (HL0 0 ltac:(lia)); lia).
all: assert (T1 : g23 < g15 -> 4 * (idx + d1) + 4 <= nF) by (intros H; pose proof (HL1 0 ltac:(lia) H); lia).
all: assert (T2 : g16 < g30 -> 4 * (idx + d2) + 4 <= nF) by (intros H; pose proof (HL2 0 ltac:(lia) H); lia).
all: assert (T3 : g16 < g30 -> g23 <> 0 -> 4 * (idx + d3) + 4 <= nF) by (intros H H'; pose proof (HL3 0 ltac:(lia) H H'); lia).
all: assert (T4 : g16 < g30 -> g23 < g15 -> 4 * (idx + d4) + 4 <= nF) by (intros H H'; pose proof (HL4 0 ltac:(lia) H H'); lia).
- assert (c = 1) by lia. subst c.
eapply SRr_mono; [apply (LDK_trip 1 idx palk ltac:(lia) ltac:(lia) T0 Hpal0 ltac:(lia) T1 T2 T3 T4 fy regs mem md HI)|].
cbn [Z.eqb Pos.eqb]. intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc' & HB' & R24 & R26 & R27 & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc'|]. split; [exact HB'|].
split; [exact R24|]. split; [exact R26|]. split; [exact R27|]. split; [exact HK|]. split; [exact HF|]. split; [exact HM | exact HX].
- eapply SRr_bind; [apply (LDK_trip c idx palk Hc ltac:(lia) T0 Hpal0 ltac:(lia) T1 T2 T3 T4 fy regs mem md HI)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & Hc1 & HB1 & R24 & R26 & R27 & HK1 & HF1 & HM1 & HX1).
replace (c =? 1) with false in Hc1 by (symmetry; apply Z.eqb_neq; lia). subst c'.
pose proof HI as (HB & HR & _ & _ & _ & Vs).
assert (HI1 : ldk_sinv fy1 regs1 mem1 md1 (c - 1) (idx + 1) (palk + 1)).
{ split; [exact HB1|]. split; [exact (ldk_regs_kept regs regs1 HK1 HR)|]. split; [exact R24|]. split; [exact R26|]. split; [exact R27|].
exact (ldk_slot_kept fy regs mem md mem1 HB HM1 Vs). }
eapply SRr_mono; [apply (IH fy1 regs1 mem1 md1 (c - 1) (idx + 1) (palk + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
[ intros j Hj; pose proof (HL0 (j + 1) ltac:(lia)); lia
| intros j Hj H; pose proof (HL1 (j + 1) ltac:(lia) H); lia
| intros j Hj H; pose proof (HL2 (j + 1) ltac:(lia) H); lia
| intros j Hj H H'; pose proof (HL3 (j + 1) ltac:(lia) H H'); lia
| intros j Hj H H'; pose proof (HL4 (j + 1) ltac:(lia) H H'); lia
| exact HI1 ]|].
intros W'' c'' _ (HW & fy' & regs' & mem' & md' & Hc' & HB' & R24' & R26' & R27' & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc'|]. split; [exact HB'|].
split; [exact R24'|]. split; [rewrite R26'; unfold w64; f_equal; lia|]. split; [rewrite R27'; unfold w64; f_equal; lia|].
split; [intros r Hr; rewrite (HK r Hr); apply HK1; exact Hr|].
split; [intros r Hr; rewrite (HF r Hr); apply HF1; exact Hr|].
split; [intros a Ha Hna; rewrite (HM a Ha Hna); apply HM1; assumption|].
intros a Ha. apply HX. apply HX1. exact Ha.
Qed.
End f.
End e.
Lemma rga_ldi_kloop {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF pb pn pix cid pos s1v d1 d2 d3 d4 g15 g16 g23 g30 c idx palk
(fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) ->
(forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i)) ->
In (pb, pn) (ablocks B lyc Sc) -> pb <= pix -> pix < pb + pn -> (pb, pn) <> (flt, nF) ->
In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= palk -> palk + (c - 1) + 766 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
sp0 - STK <= s1v + 296 -> s1v + 304 <= sp0 -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 296) 8 d1 ->
0 <= d1 < 2 ^ 29 -> 0 <= d2 < 2 ^ 29 -> 0 <= d3 < 2 ^ 29 -> 0 <= d4 < 2 ^ 29 ->
0 <= g15 < 2 ^ 64 -> 0 <= g16 < 2 ^ 64 -> 0 <= g23 < 2 ^ 64 -> 0 <= g30 < 2 ^ 64 ->
1 <= c <= 3 -> 0 <= idx -> idx + c <= 2 ^ 29 ->
(forall j, 0 <= j < c -> 4 * (idx + j) + 4 <= nF) ->
(forall j, 0 <= j < c -> g23 < g15 -> 4 * (idx + j + d1) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> 4 * (idx + j + d2) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> g23 <> 0 -> 4 * (idx + j + d3) + 4 <= nF) ->
(forall j, 0 <= j < c -> g16 < g30 -> g23 < g15 -> 4 * (idx + j + d4) + 4 <= nF) ->
getr regs 24 = w64 c -> getr regs 26 = w64 idx -> getr regs 27 = w64 palk ->
getr regs 9 = w64 s1v -> getr regs 12 = w64 pix -> getr regs 20 = Z_to_bv 64 (SB + pix / 8) ->
getr regs 15 = w64 g15 -> getr regs 16 = w64 g16 -> getr regs 23 = w64 g23 -> getr regs 30 = w64 g30 ->
getr regs 17 = w64 d2 -> getr regs 29 = w64 d3 -> getr regs 28 = w64 d4 ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDK_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDK_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LDK_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDK_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 24 = w64 0 /\ getr regs2 26 = w64 (idx + c) /\ getr regs2 27 = w64 (palk + c) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + nF) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF pb pn pix cid pos s1v d1 d2 d3 d4 g15 g16 g23 g30 c idx palk fy regs memc mdc
HJ Hfrm HinF HFW HinP HP0 HP1 HPF Hfr Hpal0 Hpal1 Hs1lo Hs1hi Vs Hd1 Hd2 Hd3 Hd4 Hg15 Hg16 Hg23 Hg30 Hc Hidx Hmax HL0 HL1 HL2 HL3 HL4
G24 G26 G27 G9 G12 G20 G15 G16 G23 G30 G17 G29 G28 G31 G25.
assert (HI : ldk_sinv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt pix s1v d1 d2 d3 d4 g15 g16 g23 g30 fy regs memc mdc c idx palk).
{ split; [repeat (split; [assumption|]); assumption|]. split; [repeat (split; [assumption|]); assumption|]. repeat (split; [assumption|]). assumption. }
eapply SRr_mono; [exact (LDK_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF HinF HFW pb pn pix cid pos s1v d1 d2 d3 d4 g15 g16 g23 g30
HinP HP0 HP1 HPF Hfr Hs1lo Hs1hi Hd1 Hd2 Hd3 Hd4 Hg15 Hg16 Hg23 Hg30
(Z.to_nat (c - 1)) fy regs memc mdc c idx palk ltac:(lia) Hc Hidx Hmax Hpal0 Hpal1 HL0 HL1 HL2 HL3 HL4 HI)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _ & _) & R24 & R26 & R27 & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (ldk_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R24|]. split; [exact R26|]. split; [exact R27|]. split; [exact HM | exact HX].
Qed.
