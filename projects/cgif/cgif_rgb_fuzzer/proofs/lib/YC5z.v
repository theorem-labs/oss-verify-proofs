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
Definition LDG_ROOT : Z := 0x83cec.
Definition LDG_HEAD : Z := 0x83fc0.
Definition LDG_LEAF : Z := 0x83d00.
Definition LDGR_CLOB : list (bv 5) := [6; 12; 13; 20; 21]%bv.
Definition LDGR_KEEP : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDGR_KEEPP : list (bv 5) := (5%bv : bv 5) :: (11%bv : bv 5) :: LDGR_KEEP.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF root t0v : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HinN : In (root, NODE_SIZE) (ablocks B lyc Sc).
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * t0v <= nF.
Definition ldgr_lits (leafv : Z) : list (option Z) := [None; None; None; None; None; None; None; None; None; Some leafv].
Definition ldgr_a1 : sv := SOff 10 50.
Definition ldgr_t0 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 50) (SLit 3)) (SOff 25 0).
Definition ldgr_regs := sr_set (sr_set sr_atoms 11%bv ldgr_a1) 5%bv ldgr_t0.
Definition ldgr_mem (leafv : Z) : smem := [ YQ0b.mkRegion (Some 10%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 37 (ldgr_lits leafv)) ].
Definition ldgr_facts : facts :=
mkFacts [ (13%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0); (10%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_LDGR (leafv : Z) : sstate := mkSS LDG_ROOT ldgr_regs (ldgr_mem leafv) None ldgr_facts.
Definition ldgr_Bx : sv := SOff 25 0.
Definition ldgr_SH : list shent := [ mkSHE 10 0 NODE_SIZE ].
Definition ldgr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ldgr_vals (c0 c1 : Z) (n : tnode) (leafv : Z) : list Z := [0; 0; 0; 0; 0] ++ node_vals c0 c1 n leafv.
Definition ldgr_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 31 = w64 flt /\ getr regs 25 = w64 SB.
Lemma ldgr_env : forall fy regs mem md, ldgr_base fy regs mem md ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\
4096 <= root /\ root + 56 <= alloc_ceiling /\ root mod 16 = 0.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ root NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF].
repeat split; try assumption; try lia.
Qed.
Lemma LDGR_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
ldgr_base fy regs mem md -> getr regs 13 = w64 t0v -> getr regs 10 = w64 root ->
getr regs 11 = w64 (root + 50) -> getr regs 5 = Z_to_bv 64 (SB + (root + 50) / 8) ->
obj_at trasegs (mrestrict (w_H W) mem) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
let E := Ereg regs (map (Z_to_bv 64) (ldgr_vals c0 c1 n leafv) ++ []) in
@st_ok trasegs fy E (ss_LDGR leafv) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDG_ROOT) mem (seg_rom trasegs))) /\
sh_ok trasegs ldgr_Bx ldgr_SH E (mrestrict (w_H W) mem) /\
bv_unsigned (ew E 10) = root /\ bv_unsigned (ew E 13) = t0v /\ bv_unsigned (ew E 31) = flt.
Proof.
intros fy regs mem md n c0 c1 leafv HB G13 G10 G11 G5 Ond Hlen3 E.
pose proof (ldgr_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qr0 & Qr1 & Qr16).
pose proof HB as (HJ & Hfrm & G31 & G25).
pose proof HJ as (HAR & _).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (ldgr_vals c0 c1 n leafv) j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (37 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (37 + j)%nat with (32 + (5 + j))%nat. apply HV. unfold ldgr_vals. exact Hj. }
assert (U13 : bv_unsigned (ew E 13) = t0v) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; clear - Ht0; lia).
assert (U31 : bv_unsigned (ew E 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E 25) = SB) by (rewrite E25; apply unsigned_lit_small; unfold SB; lia).
assert (U10 : bv_unsigned (ew E 10) = root) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (Hq : 0 <= (root + 50) / 8 <= root + 50) by (split; [apply Z.div_pos; clear - Qr0; lia | apply Z.div_le_upper_bound; clear - Qr0; lia]).
split; [|split; [|split; [exact U10 | split; [exact U13 | exact U31]]]].
- rewrite restrict_mkst_fx. unfold ss_LDGR, ldgr_regs. apply (entry_st_ok_full trasegs).
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
* rewrite G11. unfold ldgr_a1. cbn [sv_denot]. fold E. rewrite U10. reflexivity.
* rewrite G5. symmetry. apply lg_denot_of_U. unfold ldgr_t0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit. fold E. rewrite U10, U25, !Z.add_0_r.
rewrite (zcanon_id (root + 50)), (zcanon_id SB) by (unfold M64, SB; clear - Qr0 Qr1 C1; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((root + 50) / 8)) by (unfold M64; clear - Hq Qr0 Qr1 C1; lia).
rewrite zcanon_id by (unfold M64, SB; clear - Hq Qr0 Qr1 C1; lia). lia.
+ vm_compute. reflexivity.
+ unfold ldgr_mem. apply Forall_cons; [|apply Forall_nil].
eapply (region_ok_obj_gen trasegs _ _ 10 root); [exact U10 | clear - Qr0; lia | unfold NODE_SIZE; clear - Qr1 C1; lia | exact Ond | reflexivity | exact HVN | | intros i Hi; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen3.
do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ apply pairwise_disjoint_of_extents. unfold ldgr_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; exact I].
cbn [ldgr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U13, U31, E25, U10. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - C1 Ht0 Qf0 Qf1 Qf16 QnF Hlen Qr0 Qr1 Qr16. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ldgr_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E ldgr_Bx 10 root NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, ldgr_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
Qed.
Definition LDGR_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
ldgr_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r LDGR_KEEPP -> getr regs' r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Local Ltac ldgr_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold ss_LDGR, ldgr_mem in Hin; cbn [ss_mem In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Lemma LDGR_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
ldgr_base fy regs mem md -> getr regs 13 = w64 t0v -> getr regs 10 = w64 root ->
getr regs 11 = w64 (root + 50) -> getr regs 5 = Z_to_bv 64 (SB + (root + 50) / 8) ->
obj_at trasegs (mrestrict (w_H W) mem) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
leafv = 0 \/ leafv = 1 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_ROOT) mem (seg_rom trasegs)) md)
(LDGR_post fy regs mem (if leafv =? 0 then LDG_HEAD else LDG_LEAF)
(fun regs' => getr regs' 21 = w64 root /\ (leafv = 0 -> getr regs' 20 = w64 (flt + 4 * t0v)))).
Proof.
intros fy regs mem md n c0 c1 leafv HB G13 G10 G11 G5 Ond Hlen3 Hleaf.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldgr_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qr0 & Qr1 & Qr16).
pose proof HB as (HJ & Hfrm & G31 & G25).
destruct (LDGR_seed fy regs mem md n c0 c1 leafv HB G13 G10 G11 G5 Ond Hlen3) as (HS & SHOK & U10 & U13 & U31).
set (E := Ereg regs _) in HS, SHOK, U10, U13, U31.
assert (HAE : env_agree 46 E E) by (apply env_agree_refl).
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (11%bv : bv 5) HS) as P11.
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (5%bv : bv 5) HS) as P5.
cbn [ms_regs mkst] in P11, P5.
change (sr_get (ss_regs (ss_LDGR leafv)) 11%bv) with ldgr_a1 in P11.
change (sr_get (ss_regs (ss_LDGR leafv)) 5%bv) with ldgr_t0 in P5.
assert (FIN : forall E' ss' ms' md' pc', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 46 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 21 = SOff 10 0 ->
(sr_get (ss_regs ss') 20 = SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 2)) (SOff 31 0) \/ leafv = 1) ->
sr_get (ss_regs ss') 11 = ldgr_a1 -> sr_get (ss_regs ss') 5 = ldgr_t0 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LDGR_KEEP = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md')
(LDGR_post fy regs mem pc' (fun regs' => getr regs' 21 = w64 root /\ (leafv = 0 -> getr regs' 20 = w64 (flt + 4 * t0v))))).
{ intros E' ss' ms' md' pc' HS' HAE' Hpc' Hrv' Q21 Q20 Q11 Q5 QK HJ' Hk' Hp'. pose proof HAE' as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (ldgr_vals c0 c1 n leafv) ++ [])) E') by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LDGR_KEEP HS' HAE0 QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31 | rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25]|].
split.
{ split.
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (21%bv : bv 5) HS'), Q21. cbn [sv_denot]. rewrite EA, U10, Z.add_0_r by lia. reflexivity.
- intros Hl0. destruct Q20 as [Q20 | Hl1]; [|rewrite Hl0 in Hl1; discriminate Hl1].
rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (20%bv : bv 5) HS'), Q20.
apply lg_denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, !EA, U13, U31, !Z.add_0_r by lia.
rewrite (zcanon_id t0v), (zcanon_id flt) by (unfold M64; clear - Ht0 Qf0 Qf1 QnF C1 Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
rewrite zcanon_id by (unfold M64; clear - Ht0 Qf0 Qf1 QnF C1 Hlen; lia). lia. }
split.
{ intros r [<- | [<- | Hr]]; [| | exact (HKR r Hr)].
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (5%bv : bv 5) HS'), Q5, P5. exact (sv_denot_agree 46 E E' ldgr_t0 HAE' ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (11%bv : bv 5) HS'), Q11, P11. exact (sv_denot_agree 46 E E' ldgr_a1 HAE' ltac:(vm_compute; reflexivity)). }
split; [intros r; reflexivity|]. split; [exact Hk' | exact Hp']. }
destruct Hleaf as [-> | ->]; cbn [Z.eqb].
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgr_Bspan LDG_HEAD.
{ unfold ss_LDGR, ldgr_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 46 E Ey) by (env_agree_chain HAE) end.
apply (FIN _ _ _ _ LDG_HEAD HS HAEy); [reflexivity | reflexivity | reflexivity | left; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ exact (lg_kept_ro _ _ _ _ _ HFr ltac:(ldgr_ro_tac)).
+ intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
- aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgr_Bspan LDG_LEAF.
{ unfold ss_LDGR, ldgr_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 46 E Ey) by (env_agree_chain HAE) end.
apply (FIN _ _ _ _ LDG_LEAF HS HAEy); [reflexivity | reflexivity | reflexivity | right; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ exact (lg_kept_ro _ _ _ _ _ HFr ltac:(ldgr_ro_tac)).
+ intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End b.
Lemma rga_ldi_root {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF root t0v (n : tnode) c0 c1 leafv (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> In (root, NODE_SIZE) (ablocks B lyc Sc) -> 0 <= t0v < 2 ^ 29 -> 4 * t0v <= nF ->
obj_at trasegs (mrestrict (w_H W) memc) root LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat -> (leafv = 0 \/ leafv = 1) ->
getr regs 13 = w64 t0v -> getr regs 10 = w64 root -> getr regs 11 = w64 (root + 50) -> getr regs 5 = Z_to_bv 64 (SB + (root + 50) / 8) ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDG_ROOT) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if leafv =? 0 then LDG_HEAD else LDG_LEAF)) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LDGR_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 21 = w64 root /\ (leafv = 0 -> getr regs2 20 = w64 (flt + 4 * t0v)) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF root t0v n c0 c1 leafv fy regs memc mdc
HJ Hfrm HinF HinN Ht0 Hlen Ond Hlen3 Hleaf G13 G10 G11 G5 G31 G25.
assert (HB : ldgr_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LDGR_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF root t0v HinF HinN Ht0 Hlen
fy regs memc mdc n c0 c1 leafv HB G13 G10 G11 G5 Ond Hlen3 Hleaf)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & (R21 & R20) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [rewrite !getr_zero; reflexivity | vm_compute in Hr; discriminate | apply HK; cbv; tauto] |]). destruct Hin. }
split; [exact HF|]. split; [exact R21|]. split; [exact R20|]. split; [exact HM | exact HX].
Qed.
Definition LDGL_LEAF : Z := 0x83d00.
Definition LDGL_KHEAD : Z := 0x83d4c.
Definition LDGL_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 25; 28; 29; 30; 31]%bv.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (s1v leaf Wd pal pimg pg pn i : Z).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis HinN : In (leaf, NODE_SIZE) (ablocks B lyc Sc).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + i < pg + pn.
Hypothesis HNG : (leaf, NODE_SIZE) <> (pg, pn).
Hypothesis Hi : 0 <= i < 2 ^ 29. Hypothesis HWd : 0 < Wd < 2 ^ 31. Hypothesis Hpal : 0 <= pal < 2 ^ 64.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Definition ldgl_alias : sv := SAlu ALU_ADD (SOff 16 0) (SOff 38 0).
Definition ldgl_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 160 384 0 0 [YQ0b.mkChunk 160 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 360 (CVal 8 (SOff 37 0)); YQ0b.mkChunk 376 (CVal 8 (SOff 38 0))];
YQ0b.mkRegion (Some 21%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 40 []);
YQ0b.mkRegion (Some 39%nat) 0 1 0 1 [] ].
Definition ldgl_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (16%nat, mkAF 0 (2^29) 0); (21%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0);
(38%nat, mkAF 4096 140737479966720 0); (39%nat, mkAF 4096 140737479966720 0) ] [] [ (ldgl_alias, SOff 39 0) ].
Definition ss_LDGL : sstate := mkSS LDGL_LEAF sr_atoms ldgl_mem None ldgl_facts.
Definition ldgl_Bx : sv := SOff 25 0.
Definition ldgl_SH : list shent := [ mkSHE 21 0 NODE_SIZE; mkSHE 39 0 1 ].
Definition ldgl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ldgl_vals (c0 c1 : Z) (n : tnode) (leafv : Z) : list Z := [0; 0; 0; 0; Wd; pal; pimg; pimg + i] ++ node_vals c0 c1 n leafv.
Definition ldgl_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Definition ldgl_Q (regs regs' : bvmap 5 word) : Prop :=
getr regs' 12 = w64 (pimg + i) /\ getr regs' 20 = Z_to_bv 64 (SB + (pimg + i) / 8) /\ getr regs' 23 = w64 (i mod Wd) /\
getr regs' 22 = w64 (i + 1) /\ getr regs' 24 = w64 3 /\ getr regs' 26 = getr regs 14 /\ getr regs' 27 = w64 pal /\ getr regs' 10 = w64 Wd.
Definition LDGL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LDGL_KHEAD) mem' (seg_rom trasegs)) md' /\
ldgl_base fy' regs' mem' md' /\ ldgl_Q regs regs' /\
(forall r : bv 5, In r LDGL_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Local Ltac ldgl_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold ss_LDGL, ldgl_mem in Hin; cbn [ss_mem In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Lemma LDGL_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
ldgl_base fy regs mem md -> getr regs 21 = w64 leaf -> getr regs 16 = w64 i ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 160) 8 Wd -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 360) 8 pal ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg ->
obj_at trasegs (mrestrict (w_H W) mem) leaf LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGL_LEAF) mem (seg_rom trasegs)) md) (LDGL_post fy regs mem).
Proof.
intros fy regs mem md n c0 c1 leafv HB G21 G16 V160 V360 V376 Ond Hlen3.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G25 & G9). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & Hgpres & _ & Hpn0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ leaf NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ leaf NODE_SIZE pg pn HAR HinN HinG HNG) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size NODE_SIZE) with 56 in Hd.
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
set (E := Ereg regs (map (Z_to_bv 64) (ldgl_vals c0 c1 n leafv) ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (ldgl_vals c0 c1 n leafv) j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (40 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (40 + j)%nat with (32 + (8 + j))%nat. apply HV. unfold ldgl_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U16 : bv_unsigned (ew E 16) = i) by (rewrite (HE0 16%nat 16%bv eq_refl), G16; apply unsigned_lit_small; clear - Hi; lia).
assert (U21 : bv_unsigned (ew E 21) = leaf) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E 25) = SB) by (rewrite E25; apply unsigned_lit_small; unfold SB; lia).
assert (A36 : bv_unsigned (ew E 36) = Wd) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HWd; lia).
assert (A37 : bv_unsigned (ew E 37) = pal) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hpal).
assert (A38 : bv_unsigned (ew E 38) = pimg) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (A39 : bv_unsigned (ew E 39) = pimg + i) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (DN : forall j x, bv_unsigned (ew E j) = x -> sv_denot E (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
assert (HS : @st_ok trasegs fy E ss_LDGL (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGL_LEAF) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGL. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldgl_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E _ s1v 160 8 _ Wd); [exact (DN _ _ A36) | zside | zside | exact V160].
* apply (chunk_ok_val trasegs E _ s1v 360 8 _ pal); [exact (DN _ _ A37) | zside | zside | exact V360].
* apply (chunk_ok_val trasegs E _ s1v 376 8 _ pimg); [exact (DN _ _ A38) | zside | zside | exact V376].
+ eapply (region_ok_obj_gen trasegs _ _ 21 leaf); [exact U21 | lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros j Hj; lia].
intros j z Hj. destruct j; discriminate Hj.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite A39.
split; [clear - HG0 Hg4096 Hi; lia|]. split; [clear - HG1 Hgceil Hrg C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hgpres (pimg + i + o) ltac:(clear - Ho HG0 HG1 Hrg Hi; lia))).
- apply pairwise_disjoint_of_extents. unfold ldgl_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U9, U21, A39. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs HG0 HG1 Hgceil Hrg Hnceil Hd Hi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldgl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U9, U16, U21, E25, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs Hi HG0 HG1 Hg4096 Hgceil Hrg C1 Hn16 Hn4096 Hnceil. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldgl_facts f_alias alias_ok]. fold E. split; [|exact I].
unfold ldgl_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U16, A38, A39, !Z.add_0_r.
rewrite (zcanon_id i), (zcanon_id pimg) by (unfold M64; clear - Hi HG0 HG1 Hg4096 Hgceil Hrg C1; lia). f_equal; lia. }
assert (SHOK : sh_ok trasegs ldgl_Bx ldgl_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldgl_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E ldgl_Bx 21 leaf NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, ldgl_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U21.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E ldgl_Bx 39 (pimg + i) 1 (pimg + i) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 HG1 Hrg Hi; lia.
+ unfold U, ldgl_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A39.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Himg.
revert Hy Hia Himg HG0 HG1 Hrg Hi Hg4096 Hgceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HAE : env_agree 50 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDGL_LEAF) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgl_Bspan LDGL_KHEAD.
{ unfold ss_LDGL, ldgl_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact A39 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (pg + (a - pg)) by lia. apply HGW; [exact HinG | clear - Ha HG0 HG1 Hrg Hi; lia]. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 50 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (ldgl_vals c0 c1 n leafv) ++ [])) _) by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDGL_KEEP HS HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HS)).
assert (Hq : 0 <= (pimg + i) / 8 <= pimg + i) by (split; [apply Z.div_pos; clear - HG0 Hg4096 Hi; lia | apply Z.div_le_upper_bound; clear - HG0 Hg4096 Hi; lia]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ unfold ldgl_Q.
split; [rewrite (GR (12%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite EA, A39, Z.add_0_r by lia; reflexivity|].
split; [rewrite (GR (20%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff, U_SLit, !EA, A39, U25, !Z.add_0_r by lia;
rewrite (zcanon_id (pimg + i)), (zcanon_id SB) by (unfold M64, SB; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia);
change (Z.land (zcanon 3) 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
rewrite (zcanon_id ((pimg + i) / 8)) by (unfold M64; clear - Hq HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia);
rewrite zcanon_id by (unfold M64, SB; clear - Hq HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia); lia|].
split; [rewrite (GR (23%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply (U_remuw_small _ (SOff 16 0) (SOff 36 0) i Wd);
[ rewrite U_SOff, EA, U16, Z.add_0_r by lia; apply zcanon_id; unfold M64; clear - Hi; lia
| rewrite U_SOff, EA, A36, Z.add_0_r by lia; apply zcanon_id; unfold M64; clear - HWd; lia | clear - Hi; lia | exact HWd ]|].
split; [rewrite (GR (22%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite EA, U16 by lia; reflexivity|].
split; [rewrite (GR (24%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end; reflexivity|].
split; [rewrite (GR (26%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia; exact (HE0 14%nat 14%bv eq_refl)|].
split; [rewrite (GR (27%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite EA, A37, Z.add_0_r by lia; reflexivity|].
rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
cbn [sv_denot]. rewrite EA, A36, Z.add_0_r by lia. reflexivity. }
split; [exact HKR|]. split; [intros r; reflexivity|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr); [ldgl_rs_tac | exact A39 | exact Ha | clear - Hnw; lia].
Qed.
End c.
Lemma rga_ldi_leaf {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v leaf Wd pal pimg pg pn i (n : tnode) c0 c1 leafv (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
In (leaf, NODE_SIZE) (ablocks B lyc Sc) -> In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + i < pg + pn -> (leaf, NODE_SIZE) <> (pg, pn) ->
0 <= i < 2 ^ 29 -> 0 < Wd < 2 ^ 31 -> 0 <= pal < 2 ^ 64 ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 160) 8 Wd -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 360) 8 pal ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 376) 8 pimg ->
obj_at trasegs (mrestrict (w_H W) memc) leaf LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
getr regs 21 = w64 leaf -> getr regs 16 = w64 i -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGL_LEAF) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDGL_KHEAD) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
getr regs2 12 = w64 (pimg + i) /\ getr regs2 20 = Z_to_bv 64 (SB + (pimg + i) / 8) /\ getr regs2 23 = w64 (i mod Wd) /\
getr regs2 22 = w64 (i + 1) /\ getr regs2 24 = w64 3 /\ getr regs2 26 = getr regs 14 /\ getr regs2 27 = w64 pal /\ getr regs2 10 = w64 Wd /\
(forall r : bv 5, In r LDGL_KEEP -> getr regs2 r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v leaf Wd pal pimg pg pn i n c0 c1 leafv fy regs memc mdc
HJ Hfrm Hs1lo Hs1hi HinN HinG HG0 HG1 HNG Hi HWd Hpal HGW V160 V360 V376 Ond Hlen3 G21 G16 G25 G9.
assert (HB : ldgl_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LDGL_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v leaf Wd pal pimg pg pn i Hs1lo Hs1hi HinN HinG HG0 HG1 HNG Hi HWd Hpal HGW
fy regs memc mdc n c0 c1 leafv HB G21 G16 V160 V360 V376 Ond Hlen3)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & (Q12 & Q20 & Q23 & Q22 & Q24 & Q26 & Q27 & Q10) & HK & HF & HM & HX).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
repeat (split; [assumption|]). exact HX.
Qed.
Definition LDGS_C0 : Z := 0x83c70.
Definition LDGS_CLAMP : Z := 0x83c80.
Definition LDGS_T1 : Z := 0x83f90.
Definition LDGS_T2 : Z := 0x83fa0.
Definition LDGS_T2BR : Z := 0x83fa8.
Definition LDGS_LH : Z := 0x83c14.
Definition LDGS_EXIT : Z := 0x84404.
Definition LDGS_KEEP_C0 : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDGS_KEEP_T1 : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 28; 29; 30; 31]%bv.
Definition LDGS_KEEP_T2 : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section e.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variable s1v : Z.
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Definition ldgs_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Definition LDGS_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (KS : list (bv 5)) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
ldgs_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall r : bv 5, reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition ldgs_Bx : sv := SOff 25 0.
Definition ldgs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma ldgs_stack : forall fy regs mem md, ldgs_base fy regs mem md -> 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _). lia.
Qed.
Definition ldgs0_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 240 248 0 0 [YQ0b.mkChunk 240 (CVal 8 (SOff 36 0))] ].
Definition ss_LDGS0 : sstate := mkSS LDGS_C0 sr_atoms ldgs0_mem None
(mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (10%nat, mkAF 0 (2^29) 0); (16%nat, mkAF 0 (2^29) 0); (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDGS_C0_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (fmt i root : Z),
ldgs_base fy regs mem md -> getr regs 10 = w64 fmt -> getr regs 16 = w64 i -> 0 <= fmt < 2 ^ 29 -> 0 <= i < 2 ^ 29 -> 0 <= root < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 240) 8 root ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGS_C0) mem (seg_rom trasegs)) md)
(LDGS_post fy regs mem LDGS_CLAMP LDGS_KEEP_C0
(fun regs' => getr regs' 13 = w64 (fmt * i) /\ getr regs' 20 = w64 3 /\ getr regs' 21 = getr regs 14 /\ getr regs' 10 = w64 root)).
Proof.
intros fy regs mem md fmt i root HB G10 G16 Hfmt Hi Hroot Vroot.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldgs_stack fy regs mem md HB) as Rs. pose proof HB as (HJ & Hfrm & G25 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U10 : bv_unsigned (ew E 10) = fmt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hfmt; lia).
assert (U16 : bv_unsigned (ew E 16) = i) by (rewrite (HE0 16%nat 16%bv eq_refl), G16; apply unsigned_lit_small; clear - Hi; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E 36) = root).
{ pose proof (Ereg_vals regs [0; 0; 0; 0; root] [] 4%nat root eq_refl) as X. cbn [Nat.add] in X. change (Ereg regs _) with E in X. rewrite X. apply unsigned_lit_small. exact Hroot. }
assert (Hfi : 0 <= fmt * i < 2 ^ 60) by (split; [apply Z.mul_nonneg_nonneg; lia | apply (Z.le_lt_trans _ (2 ^ 29 * 2 ^ 29)); [apply Z.mul_le_mono_nonneg; lia | lia]]).
assert (HS : @st_ok trasegs fy E ss_LDGS0 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGS_C0) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGS0. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldgs0_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ s1v 240 8 _ root); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vroot].
- apply pairwise_disjoint_of_extents. unfold ldgs0_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E. rewrite U9, U10, U16, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs Hfmt Hi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldgs_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 37 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDGS_C0) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgs_Bspan LDGS_CLAMP.
{ unfold ss_LDGS0, ldgs0_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 37 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; root] ++ [])) _) by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDGS_KEEP_C0 HS HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HS)).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ split; [rewrite (GR (13%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite !U_SOff, ?EA, U10, U16, !Z.add_0_r by lia;
rewrite (zcanon_id fmt), (zcanon_id i) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia|].
split; [rewrite (GR (20%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end; reflexivity|].
split; [rewrite (GR (21%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ?EA by lia; exact (HE0 14%nat 14%bv eq_refl)|].
rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
cbn [sv_denot]. rewrite ?EA, A36, Z.add_0_r by lia. reflexivity. }
split; [exact HKR|]. split; [intros r; reflexivity|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold ss_LDGS0, ldgs0_mem in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
Definition ldgs1_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 40 304 0 0 [YQ0b.mkChunk 40 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 96 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 128 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 296 (CVal 8 (SOff 39 0))] ].
Definition ss_LDGS1 : sstate := mkSS LDGS_T1 sr_atoms ldgs1_mem None (mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDGS_T1_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (v40 v96 v128 v296 : Z),
ldgs_base fy regs mem md -> 0 <= v40 < 2 ^ 64 -> 0 <= v96 < 2 ^ 64 -> 0 <= v128 < 2 ^ 64 -> 0 <= v296 < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 40) 8 v40 -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 96) 8 v96 ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 128) 8 v128 -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 296) 8 v296 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGS_T1) mem (seg_rom trasegs)) md)
(LDGS_post fy regs mem LDGS_T2 LDGS_KEEP_T1
(fun regs' => getr regs' 27 = w64 v40 /\ getr regs' 26 = w64 v96 /\ getr regs' 24 = w64 v128 /\ getr regs' 10 = w64 v296)).
Proof.
intros fy regs mem md v40 v96 v128 v296 HB H40 H96 H128 H296 V40 V96 V128 V296.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldgs_stack fy regs mem md HB) as Rs. pose proof HB as (HJ & Hfrm & G25 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; v40; v96; v128; v296] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; v40; v96; v128; v296] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E 36) = v40) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact H40).
assert (A37 : bv_unsigned (ew E 37) = v96) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact H96).
assert (A38 : bv_unsigned (ew E 38) = v128) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact H128).
assert (A39 : bv_unsigned (ew E 39) = v296) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact H296).
assert (DN : forall j x, bv_unsigned (ew E j) = x -> sv_denot E (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
assert (HS : @st_ok trasegs fy E ss_LDGS1 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGS_T1) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGS1. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldgs1_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
+ apply (chunk_ok_val trasegs E _ s1v 40 8 _ v40); [exact (DN _ _ A36) | zside | zside | exact V40].
+ apply (chunk_ok_val trasegs E _ s1v 96 8 _ v96); [exact (DN _ _ A37) | zside | zside | exact V96].
+ apply (chunk_ok_val trasegs E _ s1v 128 8 _ v128); [exact (DN _ _ A38) | zside | zside | exact V128].
+ apply (chunk_ok_val trasegs E _ s1v 296 8 _ v296); [exact (DN _ _ A39) | zside | zside | exact V296].
- apply pairwise_disjoint_of_extents. unfold ldgs1_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E. rewrite U9, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldgs_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 40 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDGS_T1) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgs_Bspan LDGS_T2.
{ unfold ss_LDGS1, ldgs1_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 40 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; v40; v96; v128; v296] ++ [])) _) by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDGS_KEEP_T1 HS HAE0 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HS)).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ split; [rewrite (GR (27%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite ?EA, A36, Z.add_0_r by lia; reflexivity|].
split; [rewrite (GR (26%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite ?EA, A37, Z.add_0_r by lia; reflexivity|].
split; [rewrite (GR (24%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite ?EA, A38, Z.add_0_r by lia; reflexivity|].
rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
cbn [sv_denot]. rewrite ?EA, A39, Z.add_0_r by lia. reflexivity. }
split; [exact HKR|]. split; [intros r; reflexivity|].
split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
intros a Ha. apply (lg_kept_ro _ _ _ _ _ HFr); [|exact Ha].
intros rr Hin. cbn [ss_mem In] in Hin. unfold ss_LDGS1, ldgs1_mem in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. cbn [YQ0b.r_wlo YQ0b.r_whi]. lia.
Qed.
Definition ss_LDGS2 : sstate := mkSS LDGS_T2 sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDGS_T2_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (a4v fmt i1 N : Z),
ldgs_base fy regs mem md -> getr regs 14 = w64 a4v -> getr regs 10 = w64 fmt -> getr regs 22 = w64 i1 -> getr regs 7 = w64 N ->
0 <= a4v < 2 ^ 62 -> 0 <= fmt < 2 ^ 62 -> 0 <= i1 < 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGS_T2) mem (seg_rom trasegs)) md)
(LDGS_post fy regs mem (if i1 =? N then LDGS_EXIT else LDGS_LH) LDGS_KEEP_T2
(fun regs' => getr regs' 14 = w64 (a4v + fmt) /\ getr regs' 16 = w64 i1)).
Proof.
intros fy regs mem md a4v fmt i1 N HB G14 G10 G22 G7 Ha4 Hfmt Hi1 HN.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G25 & G9).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U14 : bv_unsigned (ew E 14) = a4v) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = fmt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = i1) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; exact Hi1).
assert (U7 : bv_unsigned (ew E 7) = N) by (rewrite (HE0 7%nat 7%bv eq_refl), G7; apply unsigned_lit_small; exact HN).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDGS2 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGS_T2) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGS2. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldgs_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDGS_T2) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgs_Bspan LDGS_T2BR. { apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 E Ex) by (env_agree_chain HAE) end.
assert (FIN : forall E' ss' ms' md' pc', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 32 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
(sr_get (ss_regs ss') 14 = SAlu ALU_ADD (SOff 10 0) (SOff 14 0) \/ sr_get (ss_regs ss') 14 = SAlu ALU_ADD (SOff 14 0) (SOff 10 0)) ->
sr_get (ss_regs ss') 16 = SOff 22 0 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LDGS_KEEP_T2 = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LDGS_post fy regs mem pc' LDGS_KEEP_T2 (fun regs' => getr regs' 14 = w64 (a4v + fmt) /\ getr regs' 16 = w64 i1))).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q14 Q16 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs []) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LDGS_KEEP_T2 HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ split.
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (14%bv : bv 5) HS').
destruct Q14 as [-> | ->]; apply lg_denot_of_U; rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff, !EA, U10, U14, !Z.add_0_r by lia;
rewrite (zcanon_id fmt), (zcanon_id a4v) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia.
- rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (16%bv : bv 5) HS'), Q16. cbn [sv_denot]. rewrite EA, U22, Z.add_0_r by lia. reflexivity. }
split; [exact HKR|]. split; [intros r; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok tratbl_lib_ok HS SHOK ldgs_Bspan.
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U22, U7, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_true_iff in Hc. rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgs_Bspan LDGS_LH. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LDGS_LH HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U22, U7, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff in Hc. rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldgs_Bspan LDGS_EXIT. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LDGS_EXIT HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
Qed.
End e.
Definition LDGA_LH : Z := 0x83c14.
Definition LDGA_BR0 : Z := 0x83c18.
Definition LDGA_C0 : Z := 0x83c70.
Definition LDGA_T2 : Z := 0x83fa0.
Definition LDGA_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDGA_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section f.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (flt nF s1v pimg pg pn i : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + i < pg + pn.
Hypothesis HGF : (pg, pn) <> (flt, nF).
Hypothesis Hi : 0 <= i < 2 ^ 29.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Definition ldga_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\
getr regs 31 = w64 flt /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Definition LDGA_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (d : bool) (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if d then LDGA_C0 else LDGA_T2)) mem' (seg_rom trasegs)) md' /\
ldga_base fy' regs' mem' md' /\ getr regs' 10 = getr regs 10 /\
(if d then getr regs' 22 = getr regs 22 else getr regs' 22 = w64 (i + 1)) /\
(forall r : bv 5, In r LDGA_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDGA_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition ldga_Bx : sv := SOff 25 0.
Definition ldga_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ldga_regs := sr_set sr_atoms 10%bv (SLit 4).
Definition ldga_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 16 0) (SLit 4)) (SLit 12)) (SOff 31 0), SOff 37 0); (SAlu ALU_ADD (SOff 16 0) (SOff 36 0), SOff 39 0) ].
Definition ldga_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 376 384 0 0 [YQ0b.mkChunk 376 (CVal 8 (SOff 36 0))];
YQ0b.mkRegion (Some 37%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 38 0))];
YQ0b.mkRegion (Some 39%nat) 0 1 0 1 [] ].
Definition ldga_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (16%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0);
(36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF 4096 140737479966720 2); (38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 4096 140737479966720 0) ] []
ldga_alias.
Definition ss_LDGAx : sstate := mkSS LDGA_LH ldga_regs ldga_mem None ldga_facts.
Definition ldga_SH : list shent := [ mkSHE 37 0 4; mkSHE 39 0 1 ].
Definition ldga_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 38 0)) (SOff 79 0).
Hypothesis Hlen : 4 * (4 * i + 3) + 4 <= nF.
Lemma LDGA_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv : Z),
ldga_base fy regs mem md -> getr regs 10 = w64 4 -> getr regs 16 = w64 i ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (4 * i + 3)) 4 cv -> 0 <= cv < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg; flt + 4 * (4 * i + 3); cv; pimg + i] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDGA_LH ldga_regs (sfr_atoms 64) ldga_mem None ldga_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs))) /\
sh_ok trasegs ldga_Bx ldga_SH E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 39) = pimg + i /\ bv_unsigned (ew E 16) = i.
Proof.
intros fy regs mem md cv HB G10 G16 Vimg Vc Hcv E0 E.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Qf16 & Qf0 & Qf1 & _ & _ & _ & Hnf0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Hg4096 & Hgceil & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos nF ltac:(lia)) as [_ QnF]. pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ pg pn flt nF HAR HinG HinF HGF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; pimg; flt + 4 * (4 * i + 3); cv; pimg + i] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U16 : bv_unsigned (ew E0 16) = i) by (rewrite (HE0 16%nat 16%bv eq_refl), G16; apply unsigned_lit_small; clear - Hi; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hi Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = pimg) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (A37 : bv_unsigned (ew E0 37) = flt + 4 * (4 * i + 3)) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hi Hlen; lia).
assert (A38 : bv_unsigned (ew E0 38) = cv) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A39 : bv_unsigned (ew E0 39) = pimg + i) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - HG0 HG1 Hg4096 Hgceil Hrg C1 Hi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
assert (Hf4 : (flt + 4 * (4 * i + 3)) mod 4 = 0).
{ replace (flt + 4 * (4 * i + 3)) with (flt + (4 * i + 3) * 4) by lia. rewrite Z.mod_add by lia.
clear - Qf16. pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 ss_LDGAx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGAx, ldga_regs. apply (entry_st_ok_full trasegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G10; reflexivity].
- vm_compute. reflexivity.
- unfold ldga_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ s1v 376 8 _ pimg); [exact (DN _ _ A36) | zside | zside | exact Vimg].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A37.
split; [clear - Qf0 Hi; lia|]. split; [clear - Qf1 QnF C1 Hi Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (4 * i + 3)) 0 4 _ cv); [exact (DN _ _ A38) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A39.
split; [clear - HG0 Hg4096 Hi; lia|]. split; [clear - HG1 Hgceil Hrg C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hgpres (pimg + i + o) ltac:(clear - Ho HG0 HG1 Hrg Hi; lia))).
- apply pairwise_disjoint_of_extents. unfold ldga_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A37, A39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs Qf1 QnF Hgceil Hrg HG0 HG1 Hi Hlen Hd. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [ldga_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U16, U31, E25, A36, A37, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs Hi HG0 HG1 Hg4096 Hgceil Hrg C1 Qf0 Qf1 Qf16 QnF Hlen Hcv Hf4. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldga_facts f_alias alias_ok ldga_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, U16, U31, A37, !Z.add_0_r.
change (Z.land (zcanon 4) 63) with 4.
rewrite (zcanon_id i), (zcanon_id flt), (zcanon_id 12) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hi Hlen; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (zcanon_id (i * 16)) by (unfold M64; clear - Hi; lia). rewrite (zcanon_id (i * 16 + 12)) by (unfold M64; clear - Hi; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Hi Hlen; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U16, A36, A39, !Z.add_0_r.
rewrite (zcanon_id i), (zcanon_id pimg) by (unfold M64; clear - Hi HG0 HG1 Hg4096 Hgceil Hrg C1; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trasegs ldga_Bx ldga_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldga_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trasegs (w_H W) mem E0 ldga_Bx 37 (flt + 4 * (4 * i + 3)) 4 (flt + 4 * (4 * i + 3)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hi Hlen QnF; lia.
+ unfold U, ldga_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Hi Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 ldga_Bx 39 (pimg + i) 1 (pimg + i) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 HG1 Hrg Hi; lia.
+ unfold U, ldga_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A39.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Himg.
revert Hy Hia Himg HG0 HG1 Hrg Hi Hg4096 Hgceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDGAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldga_Bx ldga_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite !HEE by lia. split; assumption.
Qed.
Local Ltac ldga_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin; unfold ldga_mem in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Lemma LDGA_eq : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldga_base fy regs mem md -> getr regs 10 = w64 4 -> getr regs 16 = w64 i ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 376) 8 pimg ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)) md) (LDGA_post fy regs mem).
Proof.
intros fy regs mem md HB G10 G16 Vimg.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _ & Hnf0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & _ & _ & _ & Hpn0).
pose proof (req_size_pos nF ltac:(lia)) as [_ QnF]. pose proof (req_size_pos pn ltac:(lia)) as [_ Hrg].
destruct (val_mem_of_present4 trasegs (mrestrict (w_H W) mem) (flt + 4 * (4 * i + 3))) as (cv & Hcv & Vc).
{ intros o Ho. destruct (proj1 (Hfpres (flt + 4 * (4 * i + 3) + o) ltac:(clear - Ho Hi Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity. }
destruct (LDGA_seed fy regs mem md cv HB G10 G16 Vimg Vc Hcv) as (HS & SHOK & HE & HEF & HU39 & HU16).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU39, HU16.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_EQ ldga_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold ldga_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldga_Bspan LDGA_C0
| _ = false => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldga_Bspan LDGA_T2 end;
[ cbn [ss_mem add_cond]; unfold ldga_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact HU39 | | apply awr_ok_nil];
cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (pg + (a - pg)) by lia; apply HGW; [exact HinG | clear - Ha HG0 HG1 Hrg Hi; lia] | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDGA_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDGA_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pimg; flt + 4 * (4 * i + 3); cv; pimg + i] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LDGA_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HSL)).
all: assert (R10 : getr (ms_regs ms) 10 = getr regs 10)
by (rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end; rewrite G10; reflexivity).
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
all: lazymatch type of Hcnd with
| _ = true => exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|]
| _ = false => exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|] end.
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [exact R10|].
all: split; [ rewrite (GR (22%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ?(proj1 HAEx) by lia; exact (HE 22%nat 22%bv eq_refl)
| rewrite ?(proj1 HAEx), HU16 by lia; reflexivity ] |].
all: split; [exact HKR|]; split; [exact HFK|]; split; [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
all: intros a Ha Hnw; apply (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr); [ldga_rs_tac | exact HU39 | exact Ha | clear - Hnw; lia].
Qed.
Definition ss_LDGAN : sstate := mkSS LDGA_LH sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0) ] [] []).
Lemma LDGA_ne : forall (fy : FPState) (regs : bvmap 5 word) mem md (fmt : Z),
ldga_base fy regs mem md -> getr regs 10 = w64 fmt -> 0 <= fmt < 2 ^ 64 -> fmt <> 4 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)) md) (LDGA_post fy regs mem).
Proof.
intros fy regs mem md fmt HB G10 Hfmt Hne.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U10 : bv_unsigned (ew E 10) = fmt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; exact Hfmt).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (HS : @st_ok trasegs fy E ss_LDGAN (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDGAN. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs ldga_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDGA_LH) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldga_Bspan LDGA_BR0. { apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HGa; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 E Ex) by (env_agree_chain HAE) end.
srr_branch_tok tratbl_lib_ok HS SHOK ldga_Bspan.
2:{ exfalso. rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U10, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact (Hne Hc). }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK ldga_Bspan LDGA_C0. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ ((10%bv : bv 5) :: (22%bv : bv 5) :: LDGA_KEEP) HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ msx HS eq_refl); cbn [ss_pc]; apply SRr_ret;
split; [reflexivity|]; exists true, fy, (ms_regs msx), (ms_mem msx); eexists; split; [reflexivity|] end.
split; [split; [exact HJ|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split; [exact (HKR (10%bv : bv 5) ltac:(left; reflexivity))|]. split; [exact (HKR (22%bv : bv 5) ltac:(right; left; reflexivity))|].
split; [intros r Hr; apply HKR; right; right; exact Hr|]. split; [intros r _; reflexivity|].
split; [| intros a Ha; apply (apresent_grows _ _ _ _ HG); exact (apresent_grows _ _ _ _ HGa Ha)].
intros a Ha _. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
Qed.
End f.
Lemma rga_ldi_head {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v pimg pg pn i fmt (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg + i < pg + pn -> (pg, pn) <> (flt, nF) -> 0 <= i < 2 ^ 29 ->
(forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j)) ->
0 <= fmt < 2 ^ 64 -> (fmt = 4 -> 4 * (4 * i + 3) + 4 <= nF) ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 376) 8 pimg ->
getr regs 10 = w64 fmt -> getr regs 16 = w64 i -> getr regs 31 = w64 flt -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDGA_LH) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (d : bool) (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if d then LDGA_C0 else LDGA_T2)) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
getr regs2 10 = getr regs 10 /\ (if d then getr regs2 22 = getr regs 22 else getr regs2 22 = w64 (i + 1)) /\
(forall r : bv 5, In r LDGA_KEEP -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDGA_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v pimg pg pn i fmt fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi HinG HG0 HG1 HGF Hi HGW Hfmt Hlen Vimg G10 G16 G31 G25 G9.
assert (HB : ldga_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
assert (POST : forall W2 c2, LDGA_post B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v pimg i fy regs memc W2 c2 ->
W2 = W /\ exists (d : bool) (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if d then LDGA_C0 else LDGA_T2)) mem2 (seg_rom trasegs)) md2 /\ frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
getr regs2 10 = getr regs 10 /\ (if d then getr regs2 22 = getr regs 22 else getr regs2 22 = w64 (i + 1)) /\
(forall r : bv 5, In r LDGA_KEEP -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDGA_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
{ intros W2 c2 (HW & d & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & R10 & R22 & HK & HF & HM & HX).
split; [exact HW|]. exists d, fy', regs2, mem2, md2. repeat (split; [assumption|]). exact HX. }
destruct (Z.eq_dec fmt 4) as [-> | Hne].
- eapply SRr_mono; [exact (LDGA_eq B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v pimg pg pn i HinF Hs1lo Hs1hi HinG HG0 HG1 HGF Hi HGW (Hlen eq_refl)
fy regs memc mdc HB G10 G16 Vimg)|]. intros W2 c2 _ H. exact (POST W2 c2 H).
- eapply SRr_mono; [exact (LDGA_ne B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v pimg i Hi fy regs memc mdc fmt HB G10 Hfmt Hne)|].
intros W2 c2 _ H. exact (POST W2 c2 H).
Qed.
