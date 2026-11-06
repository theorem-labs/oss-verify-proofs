(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/StackUpMainA.v, with its module paths and numbers changed; 14 of its 242 lines of code are new or changed and 12 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, lane StartupCert; rule 24: no function proved, start-up certificate layer). Image A'.
   The main-entry presence of the live stack [usp - 64 KiB, ly_top), from the start-up certificate cs_ok at main's
   entry with argH0 widened (the kit's Reusable/YA02.v, a working branch 87cf0d0d06f6: range 1 from
   usp + 24, range 3 = LPS's slack [entry_block_top, entry_page_top)). The layout's top bound is the driver's top_ok
   (lib/A/AD1v.v, usp - 160 <= ly_top <= usp + 3920), not a repeated constant, so stack_up_main_W1_A is the driver
   walk's premise lib/A/PresetD1pA.v H_stackup_main_A (lane StackDrv).
   - R1 half: H1 (lib/A/AD2i.v H1) hides no byte at or above TOP = usp - 8 MiB (vis has the disjunct TOP <=? z,
     Reusable/YA0e.v vis), so H1 = argH && negb argH && _ = false there.
   - Presence half: FULL, the memory at main's entry, has a byte at every address of [usp - 64 KiB, ly_top):
     [usp - 8 MiB, usp) by the KWr of every hand-off state (store_ok over Mr);
     [usp, usp + 24) by the KWords at usp + 0 / 8 / 16;
     [usp + 24, z_auxv) (argv[2..], argv NULL, envp, envp NULL) by argH0 range 1 and HM;
     [z_auxv, z_strs) (auxv, 160 B) by the 20 KWords at B5 + 24 .. B5 + 176;
     [z_strs, z_rand) (the strings) by argH0 range 2 and HM;
     [z_rand, z_rand + 16) (AT_RANDOM) by the KBlob at BR + 184;
     [z_rand + 16, ly_top) (LPS's slack; ly_top <= entry_page_top) by argH0 range 3 and HM.
   The hand-off facts are checked over all of HS_tfib_list by vm_compute (stk_chk_all). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YP08 YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB01 AD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Definition kw_at (ch : acs) (b : expr) (k : Z) : bool :=
  existsb (fun K => match K with
                    | KWord a w _ => (Nat.eqb w 8 && expr_eqb (a_base a) b && Z.eqb (a_off a) k)%bool
                    | _ => false end) (kn ch).
Lemma kw_at_In : forall ch b k, kw_at ch b k = true -> exists v, In (KWord (SA b k) 8 v) (kn ch).
Proof.
intros ch b k H. unfold kw_at in H. apply existsb_exists in H as [K [Hin HK]].
destruct K as [a w v | | | | | | | | | ]; try discriminate HK.
apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply Z.eqb_eq in H3. subst w.
destruct a as [ab ak]. cbn [a_base a_off] in H2, H3. subst ab ak. exists v. exact Hin.
Qed.
Definition KBLOB_RAND : kentry := KBlob (SA BR 184) (ELit 16) K_RND.
Definition stk_chk (ch : acs) : bool :=
  (kn_mem KWR_STACK ch && forallb (kw_at ch eSp0) [0; 8; 16]
   && forallb (fun j => kw_at ch B5 (24 + 8 * Z.of_nat j)) (seq 0 20) && kn_mem KBLOB_RAND ch)%bool.
Lemma stk_chk_all : forallb stk_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section t.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation bsb := (build_stack_bytes TPH sp argv envp uid hw rdraw).
#[local] Notation H1 := (AD2i.H1 sp rdraw inp ch E model).
Ltac inst H := try specialize (H fx); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition uS0 := ltac:(get @AD2i.uS0).
#[local] Definition uB5 := ltac:(get @AD2i.uB5).
#[local] Definition uBR := ltac:(get @AD2i.uBR).

Lemma usp_win : 140735340871680 <= usp <= 140737488355328 /\ usp mod 16 = 0.
Proof. pose proof Hsp as (L & Hh & M). unfold sp_window_lo in L. unfold sp_window_hi in Hh. lia. Qed.
Lemma img_hi_small : 0 <= img_hi TFIB < 2 ^ 32.
Proof. cbn. lia. Qed.

(* R1 half: no byte at or above TOP is hidden by H1 *)
Lemma H1_hi : forall a : word, TOP <= bv_unsigned a -> H1 a = false.
Proof.
intros a Ha. unfold AD2i.H1, hid, vis. cbv beta zeta.
replace (TOP <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
rewrite orb_true_r. cbn [orb negb].
destruct (YA02.argH0 TPH sp rdraw argv envp uid hw E a); reflexivity.
Qed.

(* the four hand-off facts, at this hand-off state *)
Lemma chk_parts : kn_mem KWR_STACK ch = true /\ forallb (kw_at ch eSp0) [0; 8; 16] = true
  /\ forallb (fun j => kw_at ch B5 (24 + 8 * Z.of_nat j)) (seq 0 20) = true /\ kn_mem KBLOB_RAND ch = true.
Proof.
pose proof (proj1 (forallb_forall _ _) stk_chk_all ch (HS_tfib_In h ch Hch)) as H. unfold stk_chk in H.
apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
exact (conj A (conj B (conj C D))).
Qed.

Lemma MR_full : forall x : word, MR x <> None -> FULL x <> None.
Proof. intros x H. unfold Mr, mrestrict in H. destruct (HID x); [exfalso; exact (H eq_refl) | exact H]. Qed.
Lemma off_hull : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> find_segment TSEGS (bv_unsigned (Z_to_bv 64 x)) 1 = None.
Proof.
intros x Hx. apply tfib_in_hull. unfold APSG.in_hull. rewrite u64_lit by (pose proof img_hi_small; lia).
apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma mbyte_full : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> mbyte TSEGS MR x <> None -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros x Hx H. apply MR_full. unfold mbyte in H. destruct (MR (Z_to_bv 64 x)) eqn:E1; [discriminate|].
rewrite (seg_rom_none_of_find TSEGS _ (off_hull x Hx)) in H. exact H.
Qed.
Lemma wview_full : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> wview TSEGS MR (Z_to_bv 64 x) <> None -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros x Hx Hw. apply MR_full. unfold wview in Hw. destruct (MR (Z_to_bv 64 x)); [discriminate|].
rewrite (off_hull x Hx) in Hw. exact Hw.
Qed.
Lemma store1_wview : forall m (a : word), RiscvSemantics.store_ok TSEGS m a 1 = true -> wview TSEGS m a <> None.
Proof. intros m a H. cbn [RiscvSemantics.store_ok] in H. destruct (wview TSEGS m a); [discriminate | discriminate H]. Qed.

(* [usp - 8 MiB, usp): the KWr *)
Lemma present_low : forall a, usp - 8388608 <= a < usp -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. pose proof chk_parts as (K & _ & _ & _). unfold KWR_STACK in K.
pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
pose proof (ho_wr TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ K) as W.
assert (Hst : estart E (SA eSp0 (-8388608)) = usp - 8388608).
{ unfold estart. cbn [a_base a_off]. pose proof uS0 as U. unfold uE in U. lia. }
assert (Hl : elenZ E (ELit 8388608) = 8388608) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
rewrite Hst, Hl in W. specialize (W (a - (usp - 8388608)) 1%nat ltac:(lia) ltac:(lia)).
replace (usp - 8388608 + (a - (usp - 8388608))) with a in W by lia.
apply wview_full; [lia|]. exact (store1_wview _ _ W).
Qed.

(* a KWord of width 8 in the hand-off kn *)
Lemma present_kw : forall b k, kw_at ch b k = true ->
  forall x, u b + k <= x < u b + k + 8 -> img_hi TFIB <= x < 2 ^ 64 -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros b k Hk x Hx Hb. destruct (kw_at_In ch b k Hk) as [v Hin].
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ Hin) as KO.
cbn [kentry_ok] in KO. destruct KO as (_ & _ & Hr).
assert (Ea : adenot E (SA b k) = Z_to_bv 64 (u b + k)) by reflexivity. rewrite Ea in Hr.
apply (proj1 (rdn_mbytes TSEGS MR 8 (u b + k) _)) in Hr as [Hl Hm].
specialize (Hm (Z.to_nat (x - (u b + k))) ltac:(lia)). rewrite Z2Nat.id in Hm by lia.
replace (u b + k + (x - (u b + k))) with x in Hm by lia.
apply mbyte_full; [exact Hb|]. rewrite Hm.
destruct (nth_error _ _) eqn:N; [discriminate|]. apply nth_error_None in N. rewrite Hl in N. lia.
Qed.

(* [z_rand, z_rand + 16): the KBlob *)
Lemma present_rand : forall x, u BR + 184 <= x < u BR + 200 -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros x Hx. pose proof chk_parts as (_ & _ & _ & K). unfold KBLOB_RAND in K.
pose proof (ho_kn TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ K) as KO.
cbn [kentry_ok] in KO. destruct KO as (_ & _ & KO).
assert (Hl : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
rewrite Hl in KO. specialize (KO (x - (u BR + 184)) ltac:(lia)).
assert (Hst : estart E (SA BR 184) = u BR + 184) by reflexivity.
rewrite Hst in KO. replace (u BR + 184 + (x - (u BR + 184))) with x in KO by lia.
apply MR_full. rewrite KO. discriminate.
Qed.

(* argH0's three ranges *)
Lemma W8 : 8 * ((Z.of_nat (length bsb) - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) / 8)
  = Z.of_nat (rand_off argv envp) - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184).
Proof.
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB. rewrite LB.
pose proof (YP08.rand_off_mod8 argv envp) as R8.
pose proof (Z.div_mod (Z.of_nat (rand_off argv envp)) 8 ltac:(lia)) as DM. rewrite R8 in DM.
replace (Z.of_nat (rand_off argv envp) + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
with ((Z.of_nat (rand_off argv envp) / 8 - 23 - Z.of_nat (length argv) - Z.of_nat (length envp)) * 8) by lia.
rewrite Z.div_mul by lia. lia.
Qed.
Lemma argH_in : forall x, usp <= x < 2 ^ 64 ->
  (usp + 24 <= x < z_auxv usp argv envp \/ z_strs usp argv envp <= x < z_rand usp argv envp
   \/ z_rand usp argv envp + 16 <= x < entry_page_top sp bsb) -> argH E (Z_to_bv 64 x) = true.
Proof.
intros x Hx H. pose proof usp_win as ((U1 & U2) & _).
pose proof (YP08.layout_facts sp argv envp Hsp Hva Hve) as (L1 & L2 & L3 & _).
pose proof (YP08.struct_size_eq argv envp) as SE. pose proof W8 as HW.
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB.
unfold YA02.argH0. cbv beta zeta. rewrite u64_lit by lia.
unfold z_rand, z_strs in *. unfold entry_block_top.
destruct H as [H|[H|H]].
- apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* an argH byte has its entry-image value, which LPS's image holds up to the page top *)
Lemma wrap_some : forall x, usp <= x < entry_page_top sp bsb -> x < 2 ^ 64 ->
  wrap_mem TPH sp argv envp uid hw rdraw (Z_to_bv 64 x) <> None.
Proof.
intros x Hx H64. pose proof usp_win as ((U1 & U2) & _).
rewrite wrap_above_sp by (rewrite u64_lit by lia; lia).
pose proof (entry_stack_image_top TPH sp argv envp uid hw rdraw) as T.
unfold stack_to_mem. cbv zeta. rewrite u64_lit by lia.
destruct (Z.leb_spec usp x) as [_|C]; [|lia].
destruct (Z.ltb_spec (x - usp) (Z.of_nat (length (entry_stack_image TPH sp argv envp uid hw rdraw)))) as [C|C]; [|lia].
destruct (nth_error _ _) eqn:N; [discriminate|]. apply nth_error_None in N. lia.
Qed.
Lemma block_le_page : usp + Z.of_nat (length bsb) <= entry_page_top sp bsb.
Proof.
unfold entry_page_top, entry_block_top, page_round_up_Z, page_size.
set (x := bv_unsigned sp + Z.of_nat (length bsb) + 4096 - 1).
pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as P. unfold x in *. lia.
Qed.
Lemma ly_le_page : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  ly_top ly <= entry_page_top sp bsb.
Proof.
intros ly Hal ((_ & Htop) & _). unfold entry_page_top, entry_block_top, page_round_up_Z, page_size.
set (x := bv_unsigned sp + Z.of_nat (length bsb) + 4096 - 1).
assert (Hx : bv_unsigned sp + 4095 <= x) by (unfold x; lia).
pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as P.
pose proof (Z.div_mod (ly_top ly) 4096 ltac:(lia)) as DT. rewrite Hal, Z.add_0_r in DT. lia.
Qed.

(* THE MAIN-ENTRY PRESENCE LEMMA (A'): with ly_top page aligned and within top_ok of usp (AD1v.top_ok; AD1g.uTop and
   AD1f.tfib_top_ok for AD1g.ly0), every byte of [usp - 64 KiB, ly_top) is present in H1 / FULL at main's entry. *)
Theorem stack_up_main_A : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  forall a, usp - 65536 <= a < ly_top ly -> apresent H1 FULL a.
Proof.
intros ly Hal Htop a Ha.
pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
pose proof (ly_le_page ly Hal Htop) as Hpg. pose proof Htop as ((_ & Htop') & _).
pose proof (YP08.layout_facts sp argv envp Hsp Hva Hve) as (L1 & L2 & L3 & _).
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB.
pose proof block_le_page as PG.
assert (ZR : z_rand usp argv envp + 16 = usp + Z.of_nat (length bsb)) by (unfold z_rand; lia).
pose proof (YP08.z_strs_rand sp argv envp) as ZS.
pose proof (proj1 Hva) as AV. pose proof (proj1 Hve) as EV.
split.
- apply H1_hi. rewrite u64_lit by lia. unfold YA02.TOP. lia.
- assert (HP : FULL (Z_to_bv 64 a) <> None).
  { destruct (Z_lt_le_dec a usp) as [C0|C0].
    { apply present_low. lia. }
    destruct (Z_lt_le_dec a (usp + 24)) as [C1|C1].
    { pose proof chk_parts as (_ & KH & _). cbn [forallb] in KH.
      apply andb_prop in KH as [K0 KH]. apply andb_prop in KH as [K8 KH]. apply andb_prop in KH as [K16 _].
      pose proof uS0 as U.
      destruct (Z_lt_le_dec a (usp + 8)); [|destruct (Z_lt_le_dec a (usp + 16))].
      - apply (present_kw eSp0 0 K0); lia.
      - apply (present_kw eSp0 8 K8); lia.
      - apply (present_kw eSp0 16 K16); lia. }
    destruct (Z_lt_le_dec a (z_auxv usp argv envp)) as [C2|C2].
    { rewrite HM by (apply argH_in; [lia | left; lia]). apply wrap_some; lia. }
    destruct (Z_lt_le_dec a (z_strs usp argv envp)) as [C3|C3].
    { pose proof chk_parts as (_ & _ & KA & _). pose proof uB5 as U5.
      pose proof (Z.div_mod (a - z_auxv usp argv envp) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (a - z_auxv usp argv envp) 8 ltac:(lia)) as P.
      set (q := (a - z_auxv usp argv envp) / 8) in *.
      assert (Hq : 0 <= q < 20) by lia.
      pose proof (proj1 (forallb_forall _ _) KA (Z.to_nat q) ltac:(apply in_seq; lia)) as Kj. cbv beta in Kj.
      rewrite Z2Nat.id in Kj by lia.
      apply (present_kw B5 (24 + 8 * q) Kj); lia. }
    destruct (Z_lt_le_dec a (z_rand usp argv envp)) as [C4|C4].
    { rewrite HM by (apply argH_in; [lia | right; left; lia]). apply wrap_some; lia. }
    destruct (Z_lt_le_dec a (z_rand usp argv envp + 16)) as [C5|C5].
    { apply present_rand. pose proof uBR as UR. lia. }
    rewrite HM by (apply argH_in; [lia | right; right; lia]). apply wrap_some; lia. }
  destruct (FULL (Z_to_bv 64 a)) as [b|] eqn:Hb; [exists b; reflexivity | exfalso; exact (HP eq_refl)].
Qed.

(* the same at the driver's world W1 (w_H W1 = H1) *)
Hypothesis H1_8 : forall a : Z, YG0f.in_band_rw a -> H1 (Z_to_bv 64 a) = H1 (Z_to_bv 64 (a - a mod 8)).
Corollary stack_up_main_W1_A : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  forall a, usp - 65536 <= a < ly_top ly -> apresent (w_H (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8)) FULL a.
Proof. exact stack_up_main_A. Qed.
End t.
End g.
