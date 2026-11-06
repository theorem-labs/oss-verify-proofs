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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC20 YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YP14 YI08 YI0c YI0g YI0d YI0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LND_HEAD : Z := 0x842b8.
Definition LND_MID : Z := 0x84334.
Definition LND_EXIT : Z := 0x84268.
Definition LND_CLOB : list (bv 5) := [6; 7; 12; 13; 28]%bv.
Definition LND_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.
Definition LND_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lnd_clob_cases : forall r : bv 5, reg_in r LND_CLOB = false -> r = 0%bv \/ In r LND_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma lnd_addr_U : forall E a c z, U E c = z -> (z = 0 \/ z = 1) -> U E a + 8 < 2 ^ 64 ->
U E (SAlu ALU_ADD a (SAlu ALU_SLL (SAlu ALU_XOR c (SLit 1)) (SLit 3))) = U E a + 8 * (1 - z).
Proof.
intros E a c z Hc Hz Ha. pose proof (U_range E a) as Hr. unfold M64 in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hc, !U_SLit.
destruct Hz as [-> | ->].
- change (zcanon (Z.shiftl (zcanon (Z.lxor 0 (zcanon 1))) (Z.land (zcanon 3) 63))) with 8. rewrite zcanon_id by (unfold M64; lia). lia.
- change (zcanon (Z.shiftl (zcanon (Z.lxor 1 (zcanon 1))) (Z.land (zcanon 3) 63))) with 0. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Section d.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (fb nF rgb : Z).
Hypothesis HinF : In (fb, nF) (ablocks B lyc Sc). Hypothesis HR0 : fb <= rgb. Hypothesis HR1 : rgb + 12 <= fb + nF.
Hypothesis HR4 : rgb mod 4 = 0.
Definition lnd_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 5 = w64 rgb /\ getr regs 25 = w64 SB.
Definition LND_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
lnd_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r LND_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LND_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lnd_env : forall fy regs mem md, lnd_base fy regs mem md ->
4096 <= fb /\ fb + req_size nF <= alloc_ceiling /\ nF <= req_size nF /\ 140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR HinF) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF]. repeat split; try assumption; lia.
Qed.
Definition lnd_litsA (cut : Z) : list (option Z) := [None; None; None; None; None; None; None; Some cut; None; None].
Definition lnd_memA (cut : Z) : smem :=
[ YQ0b.mkRegion (Some 6%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 36 (lnd_litsA cut));
YQ0b.mkRegion (Some 5%nat) 0 12 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0)); YQ0b.mkChunk 4 (CVal 4 (SOff 33 0)); YQ0b.mkChunk 8 (CVal 4 (SOff 34 0))] ].
Definition lnd_factsA : facts :=
mkFacts [ (6%nat, mkAF 4096 140737479966720 4); (5%nat, mkAF 4096 140737479966720 2); (25%nat, mkAF SB SB 0);
(32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 0 (2^32 - 1) 0); (34%nat, mkAF 0 (2^32 - 1) 0) ] [] [].
Definition ss_LNDAx (cut : Z) : sstate := mkSS LND_HEAD sr_atoms (lnd_memA cut) None lnd_factsA.
Definition lnd_Bx : sv := SOff 25 0.
Definition lnd_SHA : list shent := [ mkSHE 6 0 NODE_SIZE; mkSHE 5 0 12 ].
Definition lnd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lnd_cmp (c : nat) : sv := SF2 (FP2_cmp F_LE FMT_D) (SF1 (FP1_cvt FC_D FC_S RNE) (SF1 FP1_nanbox (SOff (32 + c) 0))) (SOff (38 + c) 0).
Definition lnd_addr (c : nat) : sv := SAlu ALU_ADD (SOff 6 0) (SAlu ALU_SLL (SAlu ALU_XOR (lnd_cmp c) (SLit 1)) (SLit 3)).
Definition lnd_valsA (v0 v1 v2 c0 c1 : Z) (n : tnode) (leafv : Z) : list Z := [v0; v1; v2; 0] ++ node_vals c0 c1 n leafv.
Lemma LND_seedA : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 v0 v1 v2 : Z),
lnd_base fy regs mem md -> getr regs 6 = w64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) -> (tn_addr n, NODE_SIZE) <> (fb, nF) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> length (tn_mean n) = 3%nat ->
val_mem trasegs (mrestrict (w_H W) mem) rgb 4 v0 -> val_mem trasegs (mrestrict (w_H W) mem) (rgb + 4) 4 v1 ->
val_mem trasegs (mrestrict (w_H W) mem) (rgb + 8) 4 v2 -> 0 <= v0 < 2 ^ 32 -> 0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) (lnd_valsA v0 v1 v2 c0 c1 n 0) ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LND_HEAD sr_atoms (sfr_atoms 64) (lnd_memA (tn_cut n)) None lnd_factsA)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LND_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs lnd_Bx lnd_SHA E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
ew E 36 = Z_to_bv 64 c0 /\ ew E 37 = Z_to_bv 64 c1 /\ bv_unsigned (ew E 6) = tn_addr n.
Proof.
intros fy regs mem md n c0 c1 v0 v1 v2 HB G6 Hinn Hnf Ond Hlen V0 V1 V2 Hv0 Hv1 Hv2 E0 E.
pose proof (lnd_env fy regs mem md HB) as (Qf0 & Qf1 & QnF & C1).
pose proof HB as (HJ & Hfrm & G5 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ (tn_addr n) NODE_SIZE fb nF HAR Hinn HinF Hnf) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size NODE_SIZE) with 56 in Hd.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (lnd_valsA v0 v1 v2 c0 c1 n 0) j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n 0) j = Some x -> ew E0 (36 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (36 + j)%nat with (32 + (4 + j))%nat. apply HV. unfold lnd_valsA. exact Hj. }
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rrgb : 4096 <= rgb /\ rgb + 12 <= 140737479966720) by (clear - HR0 HR1 Qf0 Qf1 QnF C1; lia).
assert (URN : bv_unsigned (ew E0 6) = tn_addr n) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (URG : bv_unsigned (ew E0 5) = rgb) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Rrgb; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A32 : bv_unsigned (ew E0 32) = v0) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hv0; lia).
assert (A33 : bv_unsigned (ew E0 33) = v1) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hv1; lia).
assert (A34 : bv_unsigned (ew E0 34) = v2) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hv2; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 (ss_LNDAx (tn_cut n)) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LND_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNDAx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnd_memA. repeat apply Forall_cons; try apply Forall_nil.
+ eapply (region_ok_obj_gen trasegs _ _ 6 (tn_addr n)); [exact URN | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 7 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|].
do 2 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j; discriminate Hj.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite URG.
split; [clear - Rrgb; lia|]. split; [clear - Rrgb; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ rgb 0 4 _ v0); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact V0].
* apply (chunk_ok_val trasegs E0 _ rgb 4 4 _ v1); [exact (DN _ _ A33) | zside | zside | exact V1].
* apply (chunk_ok_val trasegs E0 _ rgb 8 4 _ v2); [exact (DN _ _ A34) | zside | zside | exact V2].
- apply pairwise_disjoint_of_extents. unfold lnd_memA, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite URN, URG. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - HR0 HR1 QnF Hd. repeat split; lia.
- split; [|split; exact I].
cbn [lnd_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite URN, URG, E25, A32, A33, A34. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hn16 Hn4096 Hnceil C1 Rrgb HR4 Hv0 Hv1 Hv2. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK0 : sh_ok trasegs lnd_Bx lnd_SHA E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnd_SHA. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E0 lnd_Bx 6 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
+ unfold U, lnd_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact URN.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnd_Bx 5 rgb 12 rgb 0 12).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md fb nF _ _ HAR HinF); clear - HR0 HR1 QnF; lia.
+ unfold U, lnd_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact URG.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ fb nF HAR HinF) as Himg.
revert Hy Hia Himg HR0 HR1 QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 (ss_LNDAx (tn_cut n)) _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lnd_Bx lnd_SHA 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia.
split; [apply (HVN 0%nat); reflexivity|]. split; [apply (HVN 1%nat); reflexivity | exact URN].
Qed.
Lemma lnd_cmp_cases : forall E c, sv_denot E (lnd_cmp c) = Sem.w1 \/ sv_denot E (lnd_cmp c) = Sem.w0.
Proof. intros E c. unfold lnd_cmp. cbn [sv_denot]. rewrite fcmp_denot. destruct (fst _); [left | right]; reflexivity. Qed.
Lemma lnd_alias_ok : forall E c (b : bool), sv_denot E (lnd_cmp c) = (if b then Sem.w1 else Sem.w0) -> bv_unsigned (ew E 6) + 8 < 2 ^ 64 ->
sv_denot E (lnd_addr c) = sv_denot E (SOff 6 (if b then 0 else 8)).
Proof.
intros E c b Hb Hn. pose proof (bv_unsigned_in_range 64 (ew E 6)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
assert (HU : U E (SOff 6 0) = bv_unsigned (ew E 6)) by (rewrite U_SOff, Z.add_0_r; apply zcanon_id; unfold M64; lia).
apply U_inj. unfold lnd_addr.
rewrite (lnd_addr_U E (SOff 6 0) (lnd_cmp c) (if b then 1 else 0)).
- rewrite HU, U_SOff. destruct b; rewrite zcanon_id by (unfold M64; lia); lia.
- unfold U. rewrite Hb. destruct b; reflexivity.
- destruct b; [right | left]; reflexivity.
- rewrite HU. exact Hn.
Qed.
Local Ltac lnd_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_alias In] in Hin; unfold lnd_memA in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Lemma LND_A : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 : Z),
lnd_base fy regs mem md -> getr regs 6 = w64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) -> (tn_addr n, NODE_SIZE) <> (fb, nF) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n 0) -> tnode_wf n ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LND_HEAD) mem (seg_rom trasegs)) md)
(LND_post fy regs mem LND_MID (fun regs' => getr regs' 6 = Z_to_bv 64 c0 \/ getr regs' 6 = Z_to_bv 64 c1)).
Proof.
intros fy regs mem md n c0 c1 HB G6 Hinn Hnf Ond Hwf.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (lnd_env fy regs mem md HB) as (Qf0 & Qf1 & QnF & C1).
pose proof HB as (HJ & Hfrm & G5 & G25).
pose proof HJ as (HAR & _).
destruct Hwf as (Hcut & _ & _ & _ & Hlen & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (_ & Hn4096 & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil.
assert (Hpr : forall o, 0 <= o < 12 -> exists b, mbyte trasegs (mrestrict (w_H W) mem) (rgb + o) = Some b).
{ intros o Ho. destruct (proj1 (Hfpres (rgb + o) ltac:(clear - Ho HR0 HR1 QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity. }
destruct (val_mem_of_present4 trasegs (mrestrict (w_H W) mem) rgb) as (v0 & Hv0 & V0).
{ intros i Hi. apply Hpr. lia. }
destruct (val_mem_of_present4 trasegs (mrestrict (w_H W) mem) (rgb + 4)) as (v1 & Hv1 & V1).
{ intros i Hi. replace (rgb + 4 + i) with (rgb + (4 + i)) by lia. apply Hpr. lia. }
destruct (val_mem_of_present4 trasegs (mrestrict (w_H W) mem) (rgb + 8)) as (v2 & Hv2 & V2).
{ intros i Hi. replace (rgb + 8 + i) with (rgb + (8 + i)) by lia. apply Hpr. lia. }
destruct (LND_seedA fy regs mem md n c0 c1 v0 v1 v2 HB G6 Hinn Hnf Ond Hlen V0 V1 V2 Hv0 Hv1 Hv2) as (HS & SHOK & HE & HEF & HE36 & HE37 & HURN).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HE36, HE37, HURN.
assert (HURN8 : bv_unsigned (ew E 6) + 8 < 2 ^ 64) by (rewrite HURN; clear - Hnceil C1; lia).
assert (FIN : forall (fz : FPState) E' ss' ms' md', @st_ok trasegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = LND_MID -> ss_resv ss' = None ->
(sr_get (ss_regs ss') 6 = SOff 36 0 \/ sr_get (ss_regs ss') 6 = SOff 37 0) ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LND_KEEP = true ->
frm_zero (@fp_csr fz) -> (forall r : bv 5, In r LND_FKEEP -> reg_get (@fp_regs fz) r = reg_get (@fp_regs fy) r) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md')
(LND_post fy regs mem LND_MID (fun regs' => getr regs' 6 = Z_to_bv 64 c0 \/ getr regs' 6 = Z_to_bv 64 c1))).
{ intros fz E' ss' ms' md' HS' [EA ED] Hpc' Hrv' QRN QK Hfz HfzK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) (lnd_valsA v0 v1 v2 c0 c1 n 0) ++ [])) E').
{ split; [intros j Hj; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LND_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [rewrite (HKR (5%bv : bv 5) ltac:(cbv; tauto)); exact G5|].
rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)). exact G25. }
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (6%bv : bv 5) HS').
destruct QRN as [-> | ->]; [left | right]; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia; assumption. }
split; [exact HKR|]. split; [exact HfzK|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
assert (Hcc : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by (clear - Hcut; lia).
destruct Hcc as [Hcc | [Hcc | Hcc]]; rewrite Hcc in HS;
[ destruct (lnd_cmp_cases E 0) as [Hb | Hb] | destruct (lnd_cmp_cases E 1) as [Hb | Hb] | destruct (lnd_cmp_cases E 2) as [Hb | Hb] ].
1: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 0) (SOff 6 0) HS (lnd_alias_ok E 0 true Hb HURN8)) as HS2.
2: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 0) (SOff 6 8) HS (lnd_alias_ok E 0 false Hb HURN8)) as HS2.
3: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 1) (SOff 6 0) HS (lnd_alias_ok E 1 true Hb HURN8)) as HS2.
4: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 1) (SOff 6 8) HS (lnd_alias_ok E 1 false Hb HURN8)) as HS2.
5: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 2) (SOff 6 0) HS (lnd_alias_ok E 2 true Hb HURN8)) as HS2.
6: pose proof (st_okF_add_alias trasegs E _ _ (lnd_addr 2) (SOff 6 8) HS (lnd_alias_ok E 2 false Hb HURN8)) as HS2.
all: clear HS; rename HS2 into HS; cbv [lnd_addr lnd_cmp Nat.add] in HS.
all: aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnd_Bspan LND_MID;
[ cbn [ss_mem add_alias]; unfold lnd_memA; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LND_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LND_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: apply (FIN _ _ _ _ _ HSL HAEx); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | vm_compute; reflexivity | exact Hfrm' | exact HFK | exact HJ | | ];
[ exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnd_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha) ].
Qed.
Definition lnd_litsB (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition lnd_memB (leafv : Z) : smem := [ YQ0b.mkRegion (Some 6%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 36 (lnd_litsB leafv)) ].
Definition lnd_factsB : facts := mkFacts [ (6%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0) ] [] [].
Definition ss_LNDB (leafv : Z) : sstate := mkSS LND_MID sr_atoms (lnd_memB leafv) None lnd_factsB.
Definition lnd_SHB : list shent := [ mkSHE 6 0 NODE_SIZE ].
Lemma LND_seedB : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lnd_base fy regs mem md -> getr regs 6 = w64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
let E := Ereg regs (map (Z_to_bv 64) (lnd_valsA 0 0 0 c0 c1 n leafv) ++ []) in
@st_ok trasegs fy E (ss_LNDB leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LND_MID) mem (seg_rom trasegs))) /\
sh_ok trasegs lnd_Bx lnd_SHB E (mrestrict (w_H W) mem).
Proof.
intros fy regs mem md n c0 c1 leafv HB G6 Hinn Ond Hlen E.
pose proof (lnd_env fy regs mem md HB) as (Qf0 & Qf1 & QnF & C1).
pose proof HB as (HJ & Hfrm & G5 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (tn_addr n) NODE_SIZE HAR Hinn) as (Hn16 & Hn4096 & Hnceil & _).
change (req_size NODE_SIZE) with 56 in Hnceil.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (lnd_valsA 0 0 0 c0 c1 n leafv) j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (36 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (36 + j)%nat with (32 + (4 + j))%nat. apply HV. unfold lnd_valsA. exact Hj. }
assert (URN : bv_unsigned (ew E 6) = tn_addr n) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
split.
- rewrite restrict_mkst_fx. unfold ss_LNDB. apply (entry_st_ok_full trasegs).
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ unfold lnd_memB. apply Forall_cons; [|apply Forall_nil].
eapply (region_ok_obj_gen trasegs _ _ 6 (tn_addr n)); [exact URN | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ apply pairwise_disjoint_of_extents. unfold lnd_memB, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; exact I].
cbn [lnd_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite URN, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hn16 Hn4096 Hnceil C1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lnd_SHB. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E lnd_Bx 6 (tn_addr n) NODE_SIZE 0 NODE_SIZE HAR Hinn).
+ unfold U, lnd_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact URN.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Local Ltac lnd_roB_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold ss_LNDB, lnd_memB in Hin; cbn [ss_mem In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Lemma LND_B : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lnd_base fy regs mem md -> getr regs 6 = w64 (tn_addr n) ->
In (tn_addr n, NODE_SIZE) (ablocks B lyc Sc) ->
obj_at trasegs (mrestrict (w_H W) mem) (tn_addr n) LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
leafv = 0 \/ leafv = 1 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LND_MID) mem (seg_rom trasegs)) md)
(LND_post fy regs mem (if leafv =? 0 then LND_HEAD else LND_EXIT) (fun regs' => getr regs' 6 = getr regs 6)).
Proof.
intros fy regs mem md n c0 c1 leafv HB G6 Hinn Ond Hlen Hleaf.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G5 & G25).
destruct (LND_seedB fy regs mem md n c0 c1 leafv HB G6 Hinn Ond Hlen) as (HS & SHOK).
set (E := Ereg regs _) in HS, SHOK.
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
destruct Hleaf as [-> | ->]; cbn [Z.eqb].
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnd_Bspan LND_HEAD.
{ unfold ss_LNDB, lnd_memB. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (6%bv :: LND_KEEP) HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (5%bv : bv 5) ltac:(cbv; tauto)); exact G5 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact (HKR (6%bv : bv 5) ltac:(left; reflexivity))|].
split; [intros r Hr; apply HKR; right; exact Hr|]. split; [intros r Hr; reflexivity|].
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnd_roB_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnd_Bspan LND_EXIT.
{ unfold ss_LNDB, lnd_memB. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (6%bv :: LND_KEEP) HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (5%bv : bv 5) ltac:(cbv; tauto)); exact G5 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split; [exact (HKR (6%bv : bv 5) ltac:(left; reflexivity))|].
split; [intros r Hr; apply HKR; right; exact Hr|]. split; [intros r Hr; reflexivity|].
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnd_roB_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
Definition lnd_leafQ (t : tree) (regs' : bvmap 5 word) : Prop := exists nl, In nl (tree_leaves t) /\ getr regs' 6 = w64 (tn_addr nl).
Definition lnd_G (t : tree) : Prop :=
forall (fy : FPState) (regs : bvmap 5 word) mem md,
tree_full t -> tree_forall tnode_wf t -> tree_at trasegs (mrestrict (w_H W) mem) t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (fb, nF)) ->
(exists n l r, t = TNode n l r) -> lnd_base fy regs mem md -> getr regs 6 = w64 (troot t) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LND_HEAD) mem (seg_rom trasegs)) md) (LND_post fy regs mem LND_EXIT (lnd_leafQ t)).
Lemma lnd_post_trans : forall fy regs mem fy1 regs1 mem1 pc (Q Q' : bvmap 5 word -> Prop) W' c',
(forall r : bv 5, In r LND_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LND_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
(forall regs', Q regs' -> Q' regs') ->
LND_post fy1 regs1 mem1 pc Q W' c' -> LND_post fy regs mem pc Q' W' c'.
Proof.
intros fy regs mem fy1 regs1 mem1 pc Q Q' W' c' Hk1 Hf1 Hm1 Hp1 HQ (HW & fy' & regs' & mem' & md' & Hc & HB' & HQ' & Hk & Hf & Hm & Hp).
split; [exact HW|]. exists fy', regs', mem', md'. split; [exact Hc|]. split; [exact HB'|]. split; [exact (HQ _ HQ')|].
split; [intros r Hr; rewrite (Hk r Hr); apply Hk1; exact Hr|].
split; [intros r Hr; rewrite (Hf r Hr); apply Hf1; exact Hr|].
split; [intros a Ha; rewrite (Hm a Ha); apply Hm1; exact Ha|].
intros a Ha. apply Hp. apply Hp1. exact Ha.
Qed.
Lemma lnd_tree_kept : forall (mem mem' : word -> option byte) t,
tree_at trasegs (mrestrict (w_H W) mem) t ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> forall md, AR trasegs B lyc Sc W mem md ->
tree_at trasegs (mrestrict (w_H W) mem') t.
Proof.
intros mem mem' t Hat Hk Hin md HAR. apply (rg_tree_at_kept (w_H W) (w_H W) mem mem' t Hat).
intros b sz Hb i Hi. apply Hk. pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b sz HAR (Hin _ Hb)) as (_ & Hb4096 & Hbceil & _). lia.
Qed.
Lemma lnd_child : forall u, lnd_G u ->
forall (fy : FPState) (regs : bvmap 5 word) mem md,
tree_full u -> tree_forall tnode_wf u -> tree_at trasegs (mrestrict (w_H W) mem) u ->
(forall b, In b (tree_blocks u) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks u) -> b <> (fb, nF)) ->
lnd_base fy regs mem md -> getr regs 6 = w64 (troot u) ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LND_MID) mem (seg_rom trasegs)) md) (LND_post fy regs mem LND_EXIT (lnd_leafQ u)).
Proof.
intros u HG fy regs mem md Hfull Hwf Hat Hin Hnf HB G6.
destruct u as [|nu|nu l r]; [destruct Hfull | |].
-
cbn [tree_at troot tree_blocks] in *. destruct Hat as (_ & Hlen & c0 & c1 & Ho).
eapply SRr_mono; [exact (LND_B fy regs mem md nu c0 c1 1 HB G6 (Hin _ ltac:(left; reflexivity)) Ho Hlen ltac:(right; reflexivity))|].
cbn [Z.eqb]. intros W' c' _ H. apply (lnd_post_trans fy regs mem fy regs mem _ (fun regs' => getr regs' 6 = getr regs 6) (lnd_leafQ (TLeaf nu)) W' c' (fun r _ => eq_refl) (fun r _ => eq_refl) (fun a _ => eq_refl) (fun a Ha => Ha)); [|exact H].
intros regs' HQ. exists nu. split; [left; reflexivity|]. rewrite HQ. exact G6.
-
pose proof Hat as Hat0. cbn [tree_at troot tree_blocks] in Hat, G6, Hin. destruct Hat as (_ & Hlen & Ho & _ & _).
eapply SRr_bind; [exact (LND_B fy regs mem md nu (troot l) (troot r) 0 HB G6 (Hin _ ltac:(left; reflexivity)) Ho Hlen ltac:(left; reflexivity))|].
cbn [Z.eqb]. intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & HB1 & HQ1 & Hk1 & Hf1 & Hm1 & Hp1).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _).
eapply SRr_mono; [apply (HG fy1 regs1 mem1 md1 Hfull Hwf); [ exact (lnd_tree_kept mem mem1 _ Hat0 Hm1 Hin md HAR) | exact Hin | exact Hnf | exists nu, l, r; reflexivity | exact HB1 | rewrite HQ1; exact G6 ]|].
intros W'' c'' _ H. apply (lnd_post_trans fy regs mem fy1 regs1 mem1 _ (lnd_leafQ (TNode nu l r)) (lnd_leafQ (TNode nu l r)) W'' c'' Hk1 Hf1 Hm1 Hp1); [|exact H].
intros regs' HQ. exact HQ.
Qed.
Lemma LND_loop : forall t, lnd_G t.
Proof.
induction t as [|n|n l IHl r IHr]; intros fy regs mem md Hfull Hwf Hat Hin Hnf (n0 & l0 & r0 & Ht) HB G6; try discriminate Ht.
pose proof Hat as Hat0. cbn [tree_at] in Hat. destruct Hat as (_ & Hlen & Ho & Hl & Hr).
cbn [tree_full] in Hfull. destruct Hfull as [Fl Fr].
apply tree_forall_node in Hwf. destruct Hwf as (Wn & Wl & Wr).
cbn [troot] in G6.
assert (Hinn : In (tn_addr n, NODE_SIZE) (tree_blocks (TNode n l r))) by (left; reflexivity).
assert (Hinl : forall b, In b (tree_blocks l) -> In b (tree_blocks (TNode n l r))) by (intros b Hb; cbn [tree_blocks]; right; apply in_app_iff; left; exact Hb).
assert (Hinr : forall b, In b (tree_blocks r) -> In b (tree_blocks (TNode n l r))) by (intros b Hb; cbn [tree_blocks]; right; apply in_app_iff; right; exact Hb).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _).
eapply SRr_bind; [exact (LND_A fy regs mem md n (troot l) (troot r) HB G6 (Hin _ Hinn) (Hnf _ Hinn) Ho Wn)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & HB1 & HQ1 & Hk1 & Hf1 & Hm1 & Hp1).
destruct HQ1 as [HQ1 | HQ1].
- eapply SRr_mono; [apply (lnd_child l IHl fy1 regs1 mem1 md1 Fl Wl);
[ exact (lnd_tree_kept mem mem1 l Hl Hm1 (fun b Hb => Hin b (Hinl b Hb)) md HAR) | exact (fun b Hb => Hin b (Hinl b Hb)) | exact (fun b Hb => Hnf b (Hinl b Hb)) | exact HB1 | exact HQ1 ]|].
intros W'' c'' _ H. apply (lnd_post_trans fy regs mem fy1 regs1 mem1 _ (lnd_leafQ l) (lnd_leafQ (TNode n l r)) W'' c'' Hk1 Hf1 Hm1 Hp1); [|exact H].
intros regs' (nl & Hnl & Hr'). exists nl. split; [cbn [tree_leaves]; apply in_app_iff; left; exact Hnl | exact Hr'].
- eapply SRr_mono; [apply (lnd_child r IHr fy1 regs1 mem1 md1 Fr Wr);
[ exact (lnd_tree_kept mem mem1 r Hr Hm1 (fun b Hb => Hin b (Hinr b Hb)) md HAR) | exact (fun b Hb => Hin b (Hinr b Hb)) | exact (fun b Hb => Hnf b (Hinr b Hb)) | exact HB1 | exact HQ1 ]|].
intros W'' c'' _ H. apply (lnd_post_trans fy regs mem fy1 regs1 mem1 _ (lnd_leafQ r) (lnd_leafQ (TNode n l r)) W'' c'' Hk1 Hf1 Hm1 Hp1); [|exact H].
intros regs' (nl & Hnl & Hr'). exists nl. split; [cbn [tree_leaves]; apply in_app_iff; right; exact Hnl | exact Hr'].
Qed.
End d.
Lemma rga_lnd_descent {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fb nF rgb (t : tree) (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
tree_full t -> tree_forall tnode_wf t -> tree_at trasegs (mrestrict (w_H W) memc) t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) -> (forall b, In b (tree_blocks t) -> b <> (fb, nF)) ->
(exists n l r, t = TNode n l r) ->
getr regs 6 = w64 (troot t) -> getr regs 5 = w64 rgb -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LND_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LND_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LND_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LND_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(exists nl, In nl (tree_leaves t) /\ getr regs2 6 = w64 (tn_addr nl)) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fb nF rgb t fy regs memc mdc
HJ Hfrm HinF HR0 HR1 HR4 Hfull Hwf Hat Hin Hnf Hnode G6 G5 G25.
assert (HB : lnd_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W rgb fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LND_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W fb nF rgb HinF HR0 HR1 HR4 t fy regs memc mdc Hfull Hwf Hat Hin Hnf Hnode HB G6)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _ & _) & HQ & Hk & Hf & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lnd_clob_cases r Hr) as [-> | Hin']; [|exact (Hk r Hin')]. rewrite !getr_zero. reflexivity. }
split; [exact Hf|]. split; [exact HQ|]. split; [exact Hm | exact Hp].
Qed.
