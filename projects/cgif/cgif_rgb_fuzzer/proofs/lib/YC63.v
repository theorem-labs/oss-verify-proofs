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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LNB_ROOT : Z := 0x84254.
Definition LNB_HEAD : Z := 0x842b8.
Definition LNB_LEAF : Z := 0x84268.
Definition LNB_CLOB : list (bv 5) := [5; 6; 12]%bv.
Definition LNB_KEEP : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 10; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF s1v root t0v : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis HinN : In (root, NODE_SIZE) (ablocks B lyc Sc).
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * t0v <= nF.
Definition lnb_lits (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition lnb_a1 : sv := SOff 36 50.
Definition lnb_a7 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 50) (SLit 3)) (SOff 25 0).
Definition lnb_a6 : sv := SAlu ALU_AND (SOff 36 50) (SLit 7).
Definition lnb_regs := sr_set (sr_set (sr_set sr_atoms 11%bv lnb_a1) 17%bv lnb_a7) 16%bv lnb_a6.
Definition lnb_mem (leafv : Z) : smem :=
[ YQ0b.mkRegion (Some 9%nat) 240 248 0 0 [YQ0b.mkChunk 240 (CVal 8 (SOff 36 0))];
YQ0b.mkRegion (Some 36%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 37 (lnb_lits leafv)) ].
Definition lnb_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (5%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_LNB (leafv : Z) : sstate := mkSS LNB_ROOT lnb_regs (lnb_mem leafv) None lnb_facts.
Definition lnb_Bx : sv := SOff 25 0.
Definition lnb_SH : list shent := [ mkSHE 36 0 NODE_SIZE ].
Definition lnb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lnb_vals (c0 c1 : Z) (n : tnode) (leafv : Z) : list Z := [0; 0; 0; 0; root] ++ node_vals c0 c1 n leafv.
Definition lnb_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 31 = w64 flt /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Lemma lnb_env : forall fy regs mem md, lnb_base fy regs mem md ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\
2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v /\
4096 <= root /\ root + 56 <= alloc_ceiling /\ root mod 16 = 0.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ root NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF].
repeat split; try assumption; try lia.
Qed.
Lemma LNB_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lnb_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 11 = w64 (root + 50) -> getr regs 17 = Z_to_bv 64 (SB + (root + 50) / 8) -> getr regs 16 = Z_to_bv 64 (Z.land (root + 50) 7) ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
obj_at trasegs (mrestrict (w_H W) mem) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
let E := Ereg regs (map (Z_to_bv 64) (lnb_vals c0 c1 n leafv) ++ []) in
@st_ok trasegs fy E (ss_LNB leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNB_ROOT) mem (seg_rom trasegs))) /\
sh_ok trasegs lnb_Bx lnb_SH E (mrestrict (w_H W) mem) /\
bv_unsigned (ew E 36) = root /\ bv_unsigned (ew E 5) = t0v /\ bv_unsigned (ew E 31) = flt.
Proof.
intros fy regs mem md n c0 c1 leafv HB G5 G11 G17 G16 Vroot Ond Hlen3 E.
pose proof (lnb_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2 & Qr0 & Qr1 & Qr16).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (lnb_vals c0 c1 n leafv) j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (37 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (37 + j)%nat with (32 + (5 + j))%nat. apply HV. unfold lnb_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U5 : bv_unsigned (ew E 5) = t0v) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Ht0; lia).
assert (U31 : bv_unsigned (ew E 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E 25) = SB) by (rewrite E25; apply unsigned_lit_small; unfold SB; lia).
assert (A36 : bv_unsigned (ew E 36) = root) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (Hq : 0 <= (root + 50) / 8 <= root + 50) by (split; [apply Z.div_pos; clear - Qr0; lia | apply Z.div_le_upper_bound; clear - Qr0; lia]).
assert (Hl7 : 0 <= Z.land (root + 50) 7 <= 7).
{ replace (Z.land (root + 50) 7) with ((root + 50) mod 2 ^ 3) by (symmetry; apply (Z.land_ones (root + 50) 3); lia).
pose proof (Z.mod_pos_bound (root + 50) (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *. lia. }
split; [|split; [|split; [exact A36 | split; [exact U5 | exact U31]]]].
- rewrite restrict_mkst_fx. unfold ss_LNB, lnb_regs. apply (entry_st_ok_full trasegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
* rewrite G11. unfold lnb_a1. cbn [sv_denot]. fold E. rewrite A36. reflexivity.
* rewrite G17. symmetry. apply lg_denot_of_U. unfold lnb_a7. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit. fold E. rewrite A36, U25, !Z.add_0_r.
rewrite (zcanon_id (root + 50)), (zcanon_id SB) by (unfold M64, SB; clear - Qr0 Qr1 C1; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((root + 50) / 8)) by (unfold M64; clear - Hq Qr0 Qr1 C1; lia).
rewrite zcanon_id by (unfold M64, SB; clear - Hq Qr0 Qr1 C1; lia). lia.
* rewrite G16. symmetry. apply lg_denot_of_U. unfold lnb_a6. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit. fold E. rewrite A36.
rewrite (zcanon_id (root + 50)), (zcanon_id 7) by (unfold M64; clear - Qr0 Qr1 C1; lia).
apply zcanon_id. unfold M64. clear - Hl7. lia.
+ vm_compute. reflexivity.
+ unfold lnb_mem. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
* eapply (region_ok_obj_gen trasegs _ _ 36 root); [exact A36 | clear - Qr0; lia | unfold NODE_SIZE; clear - Qr1 C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen3.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ apply pairwise_disjoint_of_extents. unfold lnb_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U9, A36. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Qs2 Qr1. repeat split; lia.
+ split; [|split; exact I].
cbn [lnb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U9, U5, U31, E25, A36. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Ht0 Qf0 Qf1 Qf16 QnF Hlen Qr0 Qr1 Qr16. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lnb_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E lnb_Bx 36 root NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, lnb_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A36.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Definition LNB_KEEPP : list (bv 5) := (11%bv : bv 5) :: (16%bv : bv 5) :: (17%bv : bv 5) :: LNB_KEEP.
Definition LNB_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
lnb_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r LNB_KEEPP -> getr regs' r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Local Ltac lnb_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold ss_LNB, lnb_mem in Hin; cbn [ss_mem In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Lemma LNB_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lnb_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 11 = w64 (root + 50) -> getr regs 17 = Z_to_bv 64 (SB + (root + 50) / 8) -> getr regs 16 = Z_to_bv 64 (Z.land (root + 50) 7) ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
obj_at trasegs (mrestrict (w_H W) mem) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
leafv = 0 \/ leafv = 1 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNB_ROOT) mem (seg_rom trasegs)) md)
(LNB_post fy regs mem (if leafv =? 0 then LNB_HEAD else LNB_LEAF)
(fun regs' => getr regs' 6 = w64 root /\ getr regs' 5 = w64 (if leafv =? 0 then flt + 4 * t0v else t0v))).
Proof.
intros fy regs mem md n c0 c1 leafv HB G5 G11 G17 G16 Vroot Ond Hlen3 Hleaf.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (lnb_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2 & Qr0 & Qr1 & Qr16).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
destruct (LNB_seed fy regs mem md n c0 c1 leafv HB G5 G11 G17 G16 Vroot Ond Hlen3) as (HS & SHOK & A36 & U5 & U31).
set (E := Ereg regs _) in HS, SHOK, A36, U5, U31.
assert (HAE : env_agree 46 E E) by (apply env_agree_refl).
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (11%bv : bv 5) HS) as P11.
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (16%bv : bv 5) HS) as P16.
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (17%bv : bv 5) HS) as P17.
cbn [ms_regs mkst] in P11, P16, P17.
change (sr_get (ss_regs (ss_LNB leafv)) 11%bv) with lnb_a1 in P11.
change (sr_get (ss_regs (ss_LNB leafv)) 16%bv) with lnb_a6 in P16.
change (sr_get (ss_regs (ss_LNB leafv)) 17%bv) with lnb_a7 in P17.
assert (FIN : forall E' ss' ms' md' pc', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 46 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 6 = SOff 36 0 ->
(sr_get (ss_regs ss') 5 = SAlu ALU_ADD (SAlu ALU_SLL (SOff 5 0) (SLit 2)) (SOff 31 0) /\ leafv = 0 \/ sr_get (ss_regs ss') 5 = SOff 5 0 /\ leafv = 1) ->
sr_get (ss_regs ss') 11 = lnb_a1 -> sr_get (ss_regs ss') 16 = lnb_a6 -> sr_get (ss_regs ss') 17 = lnb_a7 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNB_KEEP = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md')
(LNB_post fy regs mem pc' (fun regs' => getr regs' 6 = w64 root /\ getr regs' 5 = w64 (if leafv =? 0 then flt + 4 * t0v else t0v)))).
{ intros E' ss' ms' md' pc' HS' HAE' Hpc' Hrv' Q6 Q5 Q11 Q16 Q17 QK HJ' Hk' Hp'. pose proof HAE' as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (lnb_vals c0 c1 n leafv) ++ [])) E') by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LNB_KEEP HS' HAE0 QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ split.
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (6%bv : bv 5) HS'), Q6. cbn [sv_denot]. rewrite EA, A36, Z.add_0_r by lia. reflexivity.
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (5%bv : bv 5) HS').
destruct Q5 as [[-> ->] | [-> ->]]; cbn [Z.eqb].
+ apply lg_denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, !EA, U5, U31, !Z.add_0_r by lia.
rewrite (zcanon_id t0v), (zcanon_id flt) by (unfold M64; clear - Ht0 Qf0 Qf1 QnF C1 Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
rewrite zcanon_id by (unfold M64; clear - Ht0 Qf0 Qf1 QnF C1 Hlen; lia). lia.
+ cbn [sv_denot]. rewrite EA, U5, Z.add_0_r by lia. reflexivity. }
split.
{ intros r [<- | [<- | [<- | Hr]]]; [| | | exact (HKR r Hr)].
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (11%bv : bv 5) HS'), Q11, P11. exact (sv_denot_agree 46 E E' lnb_a1 HAE' ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (16%bv : bv 5) HS'), Q16, P16. exact (sv_denot_agree 46 E E' lnb_a6 HAE' ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (17%bv : bv 5) HS'), Q17, P17. exact (sv_denot_agree 46 E E' lnb_a7 HAE' ltac:(vm_compute; reflexivity)). }
split; [intros r; reflexivity|]. split; [exact Hk' | exact Hp']. }
destruct Hleaf as [-> | ->]; cbn [Z.eqb].
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnb_Bspan LNB_HEAD.
{ unfold ss_LNB, lnb_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 46 E Ey) by (env_agree_chain HAE) end.
apply (FIN _ _ _ _ LNB_HEAD HS HAEy); [reflexivity | reflexivity | reflexivity | left; split; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnb_ro_tac)).
+ intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnb_Bspan LNB_LEAF.
{ unfold ss_LNB, lnb_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 46 E Ey) by (env_agree_chain HAE) end.
apply (FIN _ _ _ _ LNB_LEAF HS HAEy); [reflexivity | reflexivity | reflexivity | right; split; reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnb_ro_tac)).
+ intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End b.
Lemma rga_lnd_root {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v root t0v (n : tnode) c0 c1 leafv (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
In (root, NODE_SIZE) (ablocks B lyc Sc) -> 0 <= t0v < 2 ^ 29 -> 4 * t0v <= nF ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 240) 8 root ->
obj_at trasegs (mrestrict (w_H W) memc) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat -> (leafv = 0 \/ leafv = 1) ->
getr regs 5 = w64 t0v -> getr regs 11 = w64 (root + 50) -> getr regs 17 = Z_to_bv 64 (SB + (root + 50) / 8) ->
getr regs 16 = Z_to_bv 64 (Z.land (root + 50) 7) ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNB_ROOT) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if leafv =? 0 then LNB_HEAD else LNB_LEAF)) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LNB_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 6 = w64 root /\ getr regs2 5 = w64 (if leafv =? 0 then flt + 4 * t0v else t0v) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v root t0v n c0 c1 leafv fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi HinN Ht0 Hlen Vroot Ond Hlen3 Hleaf G5 G11 G17 G16 G31 G25 G9.
assert (HB : lnb_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LNB_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v root t0v HinF Hs1lo Hs1hi HinN Ht0 Hlen
fy regs memc mdc n c0 c1 leafv HB G5 G11 G17 G16 Vroot Ond Hlen3 Hleaf)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & (R6 & R5) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [rewrite !getr_zero; reflexivity | vm_compute in Hr; discriminate | apply HK; cbv; tauto] |]). destruct Hin. }
split; [exact HF|]. split; [exact R6|]. split; [exact R5|]. split; [exact HM | exact HX].
Qed.
Definition LNS_LEAF : Z := 0x84268.
Definition LNS_STORE : Z := 0x84280.
Definition LNS_BR : Z := 0x842a0.
Definition LNS_NEXT : Z := 0x84108.
Definition LNS_EXIT : Z := 0x84404.
Definition LNS_KEEP1 : list (bv 5) := [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LNS_KEEP2 : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 10; 11; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Definition lns_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 25 = w64 SB.
Definition LNS_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc lo hi : Z) (KS : list (bv 5)) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
lns_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition lns_Bx : sv := SOff 25 0.
Definition lns_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lns1_mem : smem := [ YQ0b.mkRegion (Some 6%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 37 []) ].
Definition lns1_facts : facts := mkFacts [ (6%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0) ] [] [].
Definition ss_LNS1 : sstate := mkSS LNS_LEAF sr_atoms lns1_mem None lns1_facts.
Definition lns1_SH : list shent := [ mkSHE 6 0 NODE_SIZE ].
Lemma LNS_leaf : forall (fy : FPState) (regs : bvmap 5 word) mem md (leaf : Z) (n : tnode) (c0 c1 leafv : Z),
lns_base fy regs mem md -> getr regs 6 = w64 leaf ->
In (leaf, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) mem) leaf LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_LEAF) mem (seg_rom trasegs)) md)
(LNS_post fy regs mem LNS_STORE 0 0 LNS_KEEP1 (fun _ => True)).
Proof.
intros fy regs mem md leaf n c0 c1 leafv HB G6 HinN Ond Hlen3.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G25). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ leaf NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
set (E := Ereg regs (map (Z_to_bv 64) ([0; 0; 0; 0; 0] ++ node_vals c0 c1 n leafv) ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (37 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (37 + j)%nat with (32 + (5 + j))%nat. subst E. apply Ereg_vals. exact Hj. }
assert (U6 : bv_unsigned (ew E 6) = leaf) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LNS1 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNS_LEAF) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNS1. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lns1_mem. apply Forall_cons; [|apply Forall_nil].
eapply (region_ok_obj_gen trasegs _ _ 6 leaf); [exact U6 | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. destruct j; discriminate Hj.
- apply pairwise_disjoint_of_extents. unfold lns1_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [lns1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U6, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Hn16 Hn4096 Hnceil C1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs lns_Bx lns1_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, lns1_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E lns_Bx 6 leaf NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, lns_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U6.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNS_LEAF) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lns_Bspan LNS_STORE.
{ unfold ss_LNS1, lns1_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LNS_KEEP1 HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact I|]. split; [exact HKR|]. split; [intros r; reflexivity|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha _. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold ss_LNS1, lns1_mem in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
Definition lns2_alias : sv := SAlu ALU_ADD (SOff 14 0) (SOff 36 0).
Definition lns2_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 376 384 0 0 [YQ0b.mkChunk 376 (CVal 8 (SOff 36 0))];
YQ0b.mkRegion (Some 37%nat) 0 1 0 1 [] ].
Definition lns2_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (14%nat, mkAF 0 (2^29) 0); (25%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 0);
(37%nat, mkAF 4096 140737479966720 0) ] [] [ (lns2_alias, SOff 37 0) ].
Definition ss_LNS2 : sstate := mkSS LNS_STORE sr_atoms lns2_mem None lns2_facts.
Definition lns2_SH : list shent := [ mkSHE 37 0 1 ].
Section d.
Variables (s1v pimg pg pn i N : Z).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + i < pg + pn.
Hypothesis Hi : 0 <= i < 2 ^ 29. Hypothesis HN : 0 <= N < 2 ^ 64.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Local Ltac lns2_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin; unfold ss_LNS2, lns2_mem in Hin; cbn [ss_mem In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Lemma LNS_store : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lns_base fy regs mem md -> getr regs 9 = w64 s1v -> getr regs 14 = w64 i -> getr regs 15 = w64 N ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_STORE) mem (seg_rom trasegs)) md)
(LNS_post fy regs mem (if i + 1 =? N then LNS_EXIT else LNS_NEXT) (pimg + i) (pimg + i + 1) LNS_KEEP2 (fun regs' => getr regs' 14 = w64 (i + 1))).
Proof.
intros fy regs mem md HB G9 G14 G15 Vimg.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G25). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg; pimg + i] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; pimg; pimg + i] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U14 : bv_unsigned (ew E 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi; lia).
assert (U15 : bv_unsigned (ew E 15) = N) by (rewrite (HE0 15%nat 15%bv eq_refl), G15; apply unsigned_lit_small; exact HN).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E 36) = pimg) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (A37 : bv_unsigned (ew E 37) = pimg + i) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (HS : @st_ok trasegs fy E ss_LNS2 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNS_STORE) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNS2. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lns2_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ s1v 376 8 _ pimg); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vimg].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E. rewrite A37.
split; [clear - HG0 Hg4096 Hi; lia|]. split; [clear - HG1 Hgceil Hrg C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hgpres (pimg + i + o) ltac:(clear - Ho HG0 HG1 Hrg Hi; lia))).
- apply pairwise_disjoint_of_extents. unfold lns2_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E. rewrite U9, A37.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs HG1 Hgceil Hrg. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [lns2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E.
rewrite U9, U14, E25, A36, A37. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs Hi HG0 HG1 Hg4096 Hgceil Hrg C1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lns2_facts f_alias alias_ok]. change (Ereg regs _) with E. split; [|exact I].
unfold lns2_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U14, A36, A37, !Z.add_0_r.
rewrite (zcanon_id i), (zcanon_id pimg) by (unfold M64; clear - Hi HG0 HG1 Hg4096 Hgceil Hrg C1; lia). f_equal; lia. }
assert (SHOK : sh_ok trasegs lns_Bx lns2_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, lns2_SH. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E lns_Bx 37 (pimg + i) 1 (pimg + i) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 HG1 Hrg Hi; lia.
+ unfold U, lns_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Himg.
revert Hy Hia Himg HG0 HG1 Hrg Hi Hg4096 Hgceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HAE : env_agree 38 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNS_STORE) mem (seg_rom trasegs))) in HJ, SHOK.
assert (AWR : forall Ex cs1 cs2, bv_unsigned (ew Ex 37) = pimg + i ->
awr_ok Ex [YQ0b.mkRegion (Some 9%nat) 376 384 0 0 cs1; YQ0b.mkRegion (Some 37%nat) 0 1 0 1 cs2] STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ intros Ex cs1 cs2 HU. apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen; [reflexivity | exact HU | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (pg + (a - pg)) by lia. apply HGW; [exact HinG | clear - Ha HG0 HG1 Hrg Hi; lia]. }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lns_Bspan LNS_BR. { apply AWR. exact A37. }
rename HFr into HFr1; rename HG into HG1'; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 38 E Ex) by (env_agree_chain HAE) end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (U37x : bv_unsigned (ew Ex 37) = pimg + i) by (rewrite ?(proj1 HAEx) by lia; exact A37) end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 37%nat (pimg + i) 0 1 HFr1); [lns2_rs_tac | exact A37 | exact Ha | clear - Hnw; lia]. }
assert (FIN : forall E' ss' ms' md' pc', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 38 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None -> sr_get (ss_regs ss') 14 = SOff 14 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNS_KEEP2 = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LNS_post fy regs mem pc' (pimg + i) (pimg + i + 1) LNS_KEEP2 (fun regs' => getr regs' 14 = w64 (i + 1)))).
{ intros E' ss' ms' md' pc' HS' HAE' Hpc' Hrv' Q14 QK HJ' Hk' Hp'. pose proof HAE' as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg; pimg + i] ++ [])) E') by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LNS_KEEP2 HS' HAE0 QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (14%bv : bv 5) HS'), Q14; cbn [sv_denot]; rewrite EA, U14 by lia; reflexivity|].
split; [exact HKR|]. split; [intros r; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok tratbl_lib_ok HS SHOK lns_Bspan.
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U14, U15, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; clear - Hi HN; lia).
apply Bool.negb_true_iff, Z.eqb_neq in Hc. replace (i + 1 =? N) with false by (symmetry; apply Z.eqb_neq; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lns_Bspan LNS_NEXT. { apply AWR. exact U37x. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 38 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNS_NEXT HS HAEy); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha Hnw. rewrite (lg_kept_win _ _ _ _ _ 37%nat (pimg + i) 0 1 HFr ltac:(lns2_rs_tac) U37x a Ha ltac:(clear - Hnw; lia)). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1' Ha).
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U14, U15, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; clear - Hi HN; lia).
apply Bool.negb_false_iff, Z.eqb_eq in Hc. replace (i + 1 =? N) with true by (symmetry; apply Z.eqb_eq; exact Hc).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lns_Bspan LNS_EXIT. { apply AWR. exact U37x. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 38 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNS_EXIT HS HAEy); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha Hnw. rewrite (lg_kept_win _ _ _ _ _ 37%nat (pimg + i) 0 1 HFr ltac:(lns2_rs_tac) U37x a Ha ltac:(clear - Hnw; lia)). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1' Ha).
Qed.
End d.
End c.
Lemma rga_lnd_leaf {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W leaf (n : tnode) c0 c1 leafv (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (leaf, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) memc) leaf LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
getr regs 6 = w64 leaf -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_LEAF) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LNS_STORE) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, In r LNS_KEEP1 -> getr regs2 r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W leaf n c0 c1 leafv fy regs memc mdc HJ Hfrm HinN Ond Hlen3 G6 G25.
assert (HB : lns_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fy regs memc mdc) by (split; [exact HJ|]; split; [exact Hfrm | exact G25]).
eapply SRr_mono; [exact (LNS_leaf B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fy regs memc mdc leaf n c0 c1 leafv HB G6 HinN Ond Hlen3)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & _ & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split; [exact HK|]. split; [exact HF|]. split; [intros a Ha; apply HM; [exact Ha | lia] | exact HX].
Qed.
Lemma rga_lnd_store {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v pimg pg pn i N (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + i < pg + pn -> 0 <= i < 2 ^ 29 -> 0 <= N < 2 ^ 64 ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 376) 8 pimg ->
getr regs 9 = w64 s1v -> getr regs 14 = w64 i -> getr regs 15 = w64 N -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNS_STORE) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if i + 1 =? N then LNS_EXIT else LNS_NEXT)) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
getr regs2 14 = w64 (i + 1) /\
(forall r : bv 5, In r LNS_KEEP2 -> getr regs2 r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v pimg pg pn i N fy regs memc mdc HJ Hfrm Hs1lo Hs1hi HinG HG0 HG1 Hi HN HGW Vimg G9 G14 G15 G25.
assert (HB : lns_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fy regs memc mdc) by (split; [exact HJ|]; split; [exact Hfrm | exact G25]).
eapply SRr_mono; [exact (LNS_store B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v pimg pg pn i N Hs1lo Hs1hi HinG HG0 HG1 Hi HN HGW fy regs memc mdc HB G9 G14 G15 Vimg)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & R14 & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split; [exact R14|]. split; [exact HK|]. split; [exact HF|]. split; [exact HM | exact HX].
Qed.
