(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2l.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma match_last : forall (l : list sptr) d, l <> [] ->
(match l with [] => None | x :: t => Some (last (x :: t) d) end) = Some (last l d).
Proof. intros [|x l] d H; [exfalso; exact (H eq_refl) | reflexivity]. Qed.
Lemma with_vmmaps_twice' : forall v v' m, with_vmmaps v' (with_vmmaps v m) = with_vmmaps v' m.
Proof. intros v v' m. destruct m. reflexivity. Qed.
Lemma m_vmmaps_with : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. intros h m. destruct m. reflexivity. Qed.
Lemma m_vm_lazy_with : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. destruct m. reflexivity. Qed.
Lemma m_vm_materialized_with : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. intros h m. destruct m. reflexivity. Qed.
Lemma m_halted_with : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. intros h m. destruct m. reflexivity. Qed.
Lemma lupd_app_last {T} : forall (l : list T) x y, lupd (l ++ [x]) (length l) y = l ++ [y].
Proof. induction l as [|z l IH]; intros x y; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma nth_app_last {T} : forall (l : list T) x d, nth (length l) (l ++ [x]) d = x.
Proof. induction l as [|z l IH]; intros x d; cbn; [reflexivity | apply IH]. Qed.
Lemma hd_error_nil {T} : forall (l : list T), hd_error l = None <-> l = [].
Proof. intros [|x l]; cbn; split; congruence. Qed.
Section f.
Variable B : malloc_syms.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis XC : Xclean X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis MID : midrep B L A mem md.
Hypothesis ENC : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Hypothesis ENS : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x.
Hypothesis ERRIMG : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Hypothesis SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Let A0 := set_init_done true A.
Let N := length (st_regions A).
Let LG : ledger_ok B L A md := mid_ledger _ _ _ _ _ MID.
Let LX : ledger_x L A md := mid_ledgerx _ _ _ _ _ MID.
Let NN : forall k rg, region_of A k = Some rg -> 0 <= rg_len rg := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HI)))))))).
Record open_ctx (s3 : astate) (p : sptr) (L' : layout) (md3 : Model) (Kr : Z -> Prop) : Prop := {
oc_areas : st_areas s3 = st_areas A;
oc_metas : st_metas s3 = st_metas A;
oc_ama : st_avail_meta_areas s3 = p;
oc_init : st_init_done s3 = true;
oc_rest : ctx_rest_same A s3;
oc_hd : st_area_head s3 = st_area_head A;
oc_tl : st_area_tail s3 = st_area_tail A;
oc_fh : st_free_meta_head s3 = st_free_meta_head A;
oc_sh : 0 <= st_meta_alloc_shift s3 <= 40;
oc_RGmap : forall k rg, region_of s3 k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of A k = Some rg;
oc_RGkeep : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of s3 k = Some rg;
oc_RGnonmap : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
exists rg', region_of s3 k = Some rg' /\ rg_live rg' = true /\ rg_kind rg' <> RkMap /\ rg_len rg <= rg_len rg';
oc_LIVEold : forall k rg', (k < N)%nat -> region_of s3 k = Some rg' -> rg_live rg' = true -> exists rg, region_of A k = Some rg /\ rg_live rg = true;
oc_LEN3 : (N <= length (st_regions s3))%nat;
oc_Lctx : ly_ctx L' = ly_ctx L;
oc_Lsec : ly_sec L' = ly_sec L;
oc_Lreg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r;
oc_Laln : forall k rg, (N <= k)%nat -> region_of s3 k = Some rg -> rg_live rg = true -> ly_reg L' k mod PGSZ = 0;
oc_LG3 : ledger_ok B L' s3 md3;
oc_LX3 : ledger_x L' s3 md3;
oc_MD3 : m_halted md3 = None /\ m_vm_lazy md3 = [] /\ m_vm_materialized md3 = [];
oc_Ppage : exists rg, region_of s3 (prid p) = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
PGSZ <= poff p /\ poff p + PGSZ <= rg_len rg /\ poff p mod PGSZ = 0;
oc_Pfresh : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L' p, PGSZ) (crange L e);
oc_Pnomap : forall k rg x, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg);
oc_Krdec : forall x, Kr x \/ ~ Kr x;
oc_Kr_area : forall x a, Kr x -> In a (st_areas A) -> ~ (ptr_addr L a <= x < ptr_addr L a + PGSZ);
oc_Kr_map : forall x k rg, Kr x -> region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg);
oc_Kr_img : forall x, Kr x -> ~ in_img B x;
oc_Kr_ctx : forall x, Kr x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE);
oc_Kr_nonmap : forall x, Kr x -> in_nonmap_region L' (take_st (open_st p s3)) x;
oc_layout : layout_le A L L';
oc_md : exists vm', md3 = with_vmmaps vm' md
}.
Theorem post_open_ctx : forall s3 p L' md3 Kr, open_ctx s3 p L' md3 Kr ->
let A' := take_st (open_st p s3) in let m := padd p AREA_HDR in
Inv (m :: X) R U A' ->
forall sp mem',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WO B L A p L' Kr sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 B L' mem' A' ->
(st_areas A <> [] -> forall k, (k < 8)%nat ->
mbyte (ms_segs B) mem' (ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ptr_addr L' p) 8 k))) ->
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> present mem' x) ->
(forall i, 0 <= i < PGSZ -> mbyte (ms_segs B) mem' (ptr_addr L' p + i) = Some (Z_to_bv 8 (pagebyte (ly_sec L) i))) ->
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> present mem' x) ->
midrep B L' A' mem' md3 /\ ama_ok A' /\ bounded A' /\ ptr_addr L' m <> 0 /\
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> in_nonmap_region L' A' x) /\
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> in_nonmap_region L' A' x).
Proof.
intros s3 p L' md3 Kr OC A' m HI' sp mem' Hsp FR C11 NXT NXTP PG PGP.
exact (post_open B X R U L A mem md HI XC AMA BND MID ENC ENS ERRIMG SNC s3 p L' md3
(oc_areas _ _ _ _ _ OC) (oc_metas _ _ _ _ _ OC) (oc_ama _ _ _ _ _ OC) (oc_init _ _ _ _ _ OC) (oc_rest _ _ _ _ _ OC)
(oc_hd _ _ _ _ _ OC) (oc_fh _ _ _ _ _ OC) (oc_sh _ _ _ _ _ OC) (oc_RGmap _ _ _ _ _ OC) (oc_RGkeep _ _ _ _ _ OC)
(oc_RGnonmap _ _ _ _ _ OC) (oc_LIVEold _ _ _ _ _ OC) (oc_LEN3 _ _ _ _ _ OC) (oc_Lctx _ _ _ _ _ OC) (oc_Lsec _ _ _ _ _ OC)
(oc_Lreg _ _ _ _ _ OC) (oc_Laln _ _ _ _ _ OC) (oc_LG3 _ _ _ _ _ OC) (oc_LX3 _ _ _ _ _ OC) (oc_MD3 _ _ _ _ _ OC)
HI' (oc_Ppage _ _ _ _ _ OC) (oc_Pfresh _ _ _ _ _ OC) (oc_Pnomap _ _ _ _ _ OC)
Kr (oc_Krdec _ _ _ _ _ OC) (oc_Kr_area _ _ _ _ _ OC) (oc_Kr_map _ _ _ _ _ OC) (oc_Kr_img _ _ _ _ _ OC) (oc_Kr_ctx _ _ _ _ _ OC)
sp mem' Hsp FR C11 NXT NXTP PG PGP).
Qed.
Lemma open_page_range : forall s3 p L' md3 Kr, open_ctx s3 p L' md3 Kr ->
4096 <= ptr_addr L' p /\ ptr_addr L' p + PGSZ <= alloc_ceiling /\
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> ~ in_img B x) /\ ptr_addr L' p mod PGSZ = 0.
Proof.
intros s3 p L' md3 Kr OC. destruct (oc_Ppage _ _ _ _ _ OC) as (rg & Hr & Hl & Hk & Ho1 & Ho2 & Ho3). destruct p as [r o]. cbn [prid poff] in *.
pose proof (lg_placed _ _ _ _ (oc_LG3 _ _ _ _ _ OC) r rg Hr Hl) as (Pal & Plo & Phi & Pimg). unfold ptr_addr. cbn.
split; [unfold PGSZ in *; lia|]. split; [lia|]. split; [intros x Hx; apply Pimg; lia|].
unfold PGSZ in *. rewrite Z.add_mod, Pal, Ho3 by lia. reflexivity.
Qed.
Lemma last_area_facts : st_areas A <> [] ->
let a := last (st_areas A) (SP 0%nat 0) in
In a (st_areas A) /\ st_area_tail A = Some a /\
(forall x, ptr_addr L a <= x < ptr_addr L a + PGSZ -> ~ in_img B x /\ 4096 <= x < alloc_ceiling) /\
(forall x, ptr_addr L a <= x < ptr_addr L a + PGSZ -> present mem x).
Proof.
intros Hne a. pose proof (inv_areas HI) as (_ & _ & _ & Htl & _).
assert (Ha : In a (st_areas A)) by (apply In_last; exact Hne).
split; [exact Ha|]. split; [rewrite Htl; apply match_last; exact Hne|]. split.
- intros x Hx. exact (areas_off_img B X R U L A mem md HI MID a x Ha Hx).
- intros x Hx. pose proof (mid_mem _ _ _ _ _ MID) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO. apply FO. exact Hx.
Qed.
Lemma area_head_none : st_area_head A = None <-> st_areas A = [].
Proof. pose proof (inv_areas HI) as (_ & _ & Hhd & _). rewrite Hhd. apply hd_error_nil. Qed.
Section g.
Hypothesis Haac : 0 < st_avail_meta_area_count A.
Let p := st_avail_meta_areas A.
Definition sR : astate :=
set_regions (lupd (st_regions A0) (prid p)
(let rg := nth (prid p) (st_regions A0) (mkRegion RkMap 0 [] false) in
mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg))) A0.
Definition mdR : Model := mprotect_model (w64 (ptr_addr L p)) (w64 PGSZ) md.
Lemma sR_open : openR_st A0 = open_st p sR.
Proof. reflexivity. Qed.
Lemma resv_facts : exists r o len rw, p = SP r o /\ region_of A r = Some (mkRegion RkMetaRes len rw true) /\
o mod PGSZ = 0 /\ PGSZ <= o /\ o + PGSZ * st_avail_meta_area_count A = len /\ (forall x, In x rw -> x < o).
Proof.
pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & _ & Hresv & _).
destruct (Hresv Haac) as (r & o & rg & Ep & Hr & Hk & Hl & Ho1 & Ho2 & Ho3 & Hrw).
exists r, o, (rg_len rg), (rg_rw rg). destruct rg as [k len rw lv]. cbn in *. subst k lv.
repeat split; assumption.
Qed.
Theorem open_R : open_ctx sR p L mdR (fun _ => False).
Proof.
destruct resv_facts as (r & o & len & rw & Ep & Hr & Ho1 & Ho2 & Ho3 & Hrw).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3). pose proof (proj1 alloc_ceiling_val) as AC.
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (HrN : (r < N)%nat) by exact (region_of_lt _ _ _ Hr).
assert (Hnth : nth r (st_regions A) (mkRegion RkMap 0 [] false) = mkRegion RkMetaRes len rw true).
{ unfold region_of in Hr. exact (nth_error_nth _ _ _ Hr). }
assert (ER : st_regions sR = lupd (st_regions A) r (mkRegion RkMetaRes len (rw ++ [o]) true)).
{ unfold sR. rewrite Ep. cbn [prid poff st_regions set_regions set_init_done A0]. change (st_regions A0) with (st_regions A). rewrite Hnth. reflexivity. }
pose proof (fun k => region_of_updk A sR r _ k ER) as RO. cbn beta in RO. fold N in RO.
assert (ROr : region_of sR r = Some (mkRegion RkMetaRes len (rw ++ [o]) true)).
{ rewrite RO, Nat.eqb_refl. replace (r <? N)%nat with true by (symmetry; apply Nat.ltb_lt; exact HrN). reflexivity. }
assert (ROo : forall k, k <> r -> region_of sR k = region_of A k) by (intros k Hk; rewrite RO, (proj2 (Nat.eqb_neq _ _) Hk); reflexivity).
assert (Ho4 : o + PGSZ <= len) by nia.
assert (Hnin : ~ In o rw) by (intros Hin; pose proof (Hrw o Hin); lia).
assert (LGX : ledger_ok B L sR mdR /\ ledger_x L sR mdR).
{ unfold mdR. rewrite Ep. unfold ptr_addr. cbn [loc_addr].
exact (ledger_mprotect B L A md LG LX (conj M1 (conj M2 M3)) sR r len rw o Hr ltac:(lia) Ho4 Ho1 Hnin ER eq_refl). }
pose proof (lg_placed _ _ _ _ LG r _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi, Pimg.
assert (Ep' : ptr_addr L p = ly_reg L r + o) by (rewrite Ep; reflexivity).
assert (FRESH : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L p, PGSZ) (crange L e)).
{ intros e He. rewrite Ep'.
destruct (In_footprint_inv A e He) as [-> | [(a & Ha & ->) | (k & rg & Hk & Hkd & Hl & ->)]]; unfold ranges_disjoint, crange; cbn [fst snd loc_addr].
- rewrite (mid_ctx _ _ _ _ _ MID).
destruct (Z_le_gt_dec (ly_reg L r + o + PGSZ) (ms_ctx B)) as [|H1]; [left; lia|]. right.
destruct (Z_le_gt_dec (ms_ctx B + CTX_SIZE) (ly_reg L r + o)) as [|H2]; [lia|]. exfalso.
pose proof (so_ctx_img _ (mid_syms _ _ _ _ _ MID)) as CI.
destruct (Z_le_gt_dec (ms_ctx B) (ly_reg L r + o)).
+ apply (Pimg (ly_reg L r + o)); [lia|]. apply CI. lia.
+ apply (Pimg (ms_ctx B)); [lia|]. apply CI. unfold CTX_SIZE. lia.
- pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas a Ha) as (r' & o' & rg' & -> & Ao1 & Ao2 & Ar & Al & Alen & Akind).
cbn [loc_addr]. destruct (Nat.eq_dec r' r) as [->|Hne].
+ rewrite Hr in Ar. injection Ar as <-. cbn in Akind, Alen. pose proof (Hrw o' Akind).
apply Z.mod_divide in Ao1; [|lia]. apply Z.mod_divide in Ho1; [|lia]. destruct Ao1 as [q Hq]. destruct Ho1 as [q' Hq']. right. nia.
+ pose proof (lx_regs _ _ _ LX r r' _ rg' ltac:(congruence) Hr Ar eq_refl Al ltac:(cbn; lia)) as D.
assert (RL : reg_lo rg' < rg_len rg') by (unfold reg_lo; destruct (rg_kind rg'); lia).
specialize (D RL). unfold ranges_disjoint, reg_lo in D. cbn [rg_kind rg_len fst snd] in D.
destruct (rg_kind rg'); [ | | destruct Akind]; lia.
- assert (Hne : r <> k) by (intros ->; rewrite Hk in Hr; injection Hr as E1; subst rg; discriminate).
pose proof (lx_regs _ _ _ LX r k _ rg Hne Hr Hk eq_refl Hl ltac:(cbn; lia)) as D.
unfold reg_lo in D. rewrite Hkd in D. cbn [rg_kind rg_len] in D.
assert (LEN : 0 < rg_len rg).
{ pose proof (NN k rg Hk) as N0. destruct (lx_maps _ _ _ LX _ (lg_maps _ _ _ _ LG k rg Hk Hl ltac:(rewrite Hkd; discriminate))) as [P _].
unfold iv_len in P. cbn [snd] in P. destruct (Z.eq_dec (rg_len rg) 0) as [E0|]; [| lia]. rewrite E0 in P. change (bv_unsigned (w64 0)) with 0 in P. lia. }
specialize (D ltac:(lia)). unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
split.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- repeat split; reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- destruct BND as (_ & B2 & _). exact B2.
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ROr in Hk; injection Hk as <-; discriminate | rewrite (ROo k Hne) in Hk; exact Hk].
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite Hr in Hk; injection Hk as <-; discriminate | rewrite (ROo k Hne); exact Hk].
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne].
+ rewrite Hr in Hk. injection Hk as <-. eexists. split; [exact ROr|]. cbn. repeat split; try discriminate. lia.
+ exists rg. rewrite (ROo k Hne). auto with zarith.
- intros k rg' Hk H' Hl. destruct (Nat.eq_dec k r) as [->|Hne]; [eexists; split; [exact Hr | reflexivity] | rewrite (ROo k Hne) in H'; exists rg'; auto].
- unfold N. rewrite ER, length_lupd. lia.
- reflexivity.
- reflexivity.
- intros; reflexivity.
- intros k rg Hk H' _. exfalso. pose proof (region_of_lt _ _ _ H') as LT. rewrite ER, length_lupd in LT. unfold N in Hk. lia.
- exact (proj1 LGX).
- exact (proj2 LGX).
- unfold mdR. rewrite mprotect_model_halted, mprotect_model_lazy. split; [exact M1|]. split; [exact M2|]. unfold mprotect_model, mprotect_model_next, with_vmmaps. cbn. exact M3.
- exists (mkRegion RkMetaRes len (rw ++ [o]) true). rewrite Ep. cbn [prid poff]. split; [exact ROr|]. cbn. repeat split; try discriminate; lia.
- exact FRESH.
- intros k rg x Hk Hl Hkd Hx Hxr. pose proof (FRESH _ (footprint_region_In A k rg Hk Hkd Hl)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D. lia.
- intros x. right. intros [].
- intros x a [].
- intros x k rg [].
- intros x [].
- intros x [].
- intros x [].
- apply layout_le_refl.
- eexists. unfold mdR, mprotect_model, mprotect_model_next. reflexivity.
Qed.
End g.
Lemma point_disjoint : forall lo1 n1 lo2 n2, 0 < n1 -> 0 < n2 ->
(forall x, lo2 <= x < lo2 + n2 -> ~ (lo1 <= x < lo1 + n1)) -> ranges_disjoint (lo1, n1) (lo2, n2).
Proof.
intros lo1 n1 lo2 n2 H1 H2 H. unfold ranges_disjoint. cbn [fst snd].
destruct (Z_le_gt_dec (lo1 + n1) lo2); [left; lia|]. destruct (Z_le_gt_dec (lo2 + n2) lo1); [right; lia|]. exfalso.
destruct (Z_le_gt_dec lo1 lo2); [apply (H lo2); lia | apply (H lo1); lia].
Qed.
Lemma live_map_len : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> 0 < rg_len rg.
Proof.
intros k rg Hk Hl Hkd. pose proof (NN k rg Hk) as N0.
destruct (lx_maps _ _ _ LX _ (lg_maps _ _ _ _ LG k rg Hk Hl ltac:(rewrite Hkd; discriminate))) as [P _].
unfold iv_len in P. cbn [snd] in P. destruct (Z.eq_dec (rg_len rg) 0) as [E0|]; [| lia]. rewrite E0 in P. change (bv_unsigned (w64 0)) with 0 in P. lia.
Qed.
Lemma footprint_fresh : forall a n, 0 < n ->
(forall x, in_img B x -> ~ (a <= x < a + n)) ->
(forall k rg x, region_of A k = Some rg -> rg_live rg = true -> ly_reg L k + reg_lo rg <= x < ly_reg L k + rg_len rg -> ~ (a <= x < a + n)) ->
forall e, In e (footprint A) -> ranges_disjoint (a, n) (crange L e).
Proof.
intros a n Hn FI FRG e He.
destruct (In_footprint_inv A e He) as [-> | [(ar & Ha & ->) | (k & rg & Hk & Hkd & Hl & ->)]]; unfold crange; cbn [fst snd loc_addr].
- rewrite (mid_ctx _ _ _ _ _ MID). apply point_disjoint; [exact Hn | unfold CTX_SIZE; lia |].
intros x Hx. apply FI. apply (so_ctx_img _ (mid_syms _ _ _ _ _ MID)). lia.
- pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas ar Ha) as (r' & o' & rg' & -> & Ao1 & Ao2 & Ar & Al & Alen & Akind).
cbn [loc_addr]. apply point_disjoint; [exact Hn | unfold PGSZ; lia |].
intros x Hx. apply (FRG r' rg' x Ar Al). unfold reg_lo. destruct (rg_kind rg'); [ | | destruct Akind]; lia.
- apply point_disjoint; [exact Hn | exact (live_map_len k rg Hk Hl Hkd) |].
intros x Hx. apply (FRG k rg x Hk Hl). unfold reg_lo. rewrite Hkd. lia.
Qed.
Section j.
Variables (r : nat) (pages : Z) (md' : Model).
Hypothesis Hbk : st_brk A = BrkCur r pages.
Let b := vm_brk (m_vmmaps md).
Hypothesis Gceil : bv_unsigned b + PGSZ <= alloc_ceiling.
Hypothesis Gfree : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) b (Z_to_bv 64 PGSZ) = true.
Hypothesis MD' : md' = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, Z_to_bv 64 PGSZ) :: vm_maps (m_vmmaps md))
(vm_noaccess (m_vmmaps md)) (vm_start_brk (m_vmmaps md)) (Z_to_bv 64 (bv_unsigned b + PGSZ))
(vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md.
Let p := SP r (PGSZ * pages).
Definition sBC : astate := brk1_st r pages A0.
Lemma brk_facts : exists rw, region_of A r = Some (mkRegion RkBrk (PGSZ * pages) rw true) /\ 2 <= pages /\
bv_unsigned b = ly_reg L r + PGSZ * pages /\ ly_reg L r = ly_brk0 L.
Proof.
pose proof (inv_areas HI) as (_ & _ & _ & _ & Hres & _ & Hb & _). rewrite Hbk in Hb. destruct Hb as (Hbr & rg & Hr & Hl & Hlen & Hp).
pose proof (lg_brk _ _ _ _ LG) as LB. rewrite Hbk in LB. destruct LB as [LB1 LB2].
assert (K : rg_kind rg = RkBrk).
{ assert (Hin : In r (brk_regions A)) by (rewrite Hbr; left; reflexivity).
unfold brk_regions in Hin. apply in_flat_map in Hin as (k & _ & Hk). destruct (region_of A k) as [rg'|] eqn:Ek; [|destruct Hk].
destruct (rg_kind rg') eqn:Ek'; try (destruct Hk; fail); destruct Hk as [<-|[]]. rewrite Ek in Hr. injection Hr as ->. exact Ek'. }
exists (rg_rw rg). destruct rg as [kd ln rw lv]. cbn in *. subst kd lv ln. auto.
Qed.
Theorem open_BC : open_ctx sBC p L md' (fun _ => False).
Proof.
destruct brk_facts as (rw & Hr & Hp2 & Hb & Hr0).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range b) as Ub.
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (HrN : (r < N)%nat) by exact (region_of_lt _ _ _ Hr).
assert (Hnth : nth r (st_regions A) (mkRegion RkMap 0 [] false) = mkRegion RkBrk (PGSZ * pages) rw true).
{ unfold region_of in Hr. exact (nth_error_nth _ _ _ Hr). }
assert (ER : st_regions sBC = lupd (st_regions A) r (mkRegion RkBrk (PGSZ * pages + PGSZ) [] true)).
{ unfold sBC, brk1_st. cbn [st_regions set_avail_meta_area_count set_avail_meta_areas set_brk set_regions].
change (st_regions A0) with (st_regions A). rewrite Hnth. reflexivity. }
pose proof (fun k => region_of_updk A sBC r _ k ER) as RO. cbn beta in RO. fold N in RO.
assert (ROr : region_of sBC r = Some (mkRegion RkBrk (PGSZ * pages + PGSZ) [] true)).
{ rewrite RO, Nat.eqb_refl. replace (r <? N)%nat with true by (symmetry; apply Nat.ltb_lt; exact HrN). reflexivity. }
assert (ROo : forall k, k <> r -> region_of sBC k = region_of A k) by (intros k Hk; rewrite RO, (proj2 (Nat.eqb_neq _ _) Hk); reflexivity).
assert (Ep : ptr_addr L p = bv_unsigned b) by (unfold p, ptr_addr; cbn; lia).
assert (LGX : ledger_ok B L sBC md' /\ ledger_x L sBC md').
{ apply (ledger_grow_brk B L A md LG LX NN sBC md' r pages (PGSZ * pages) rw Hbk Hr eq_refl Hp2 Gceil Gfree ER);
rewrite ?MD', ?m_vmmaps_with, ?m_vm_lazy_with, ?m_vm_materialized_with; try reflexivity; try assumption.
cbn [vm_brk]. apply u64_w64. unfold b, PGSZ in *. lia. }
pose proof (lg_placed _ _ _ _ LG r _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi, Pimg.
pose proof (fresh_region L A md LX b PGSZ ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FRG.
pose proof (fresh_img B L A md LG b PGSZ ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FI.
assert (FRESH : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L p, PGSZ) (crange L e)).
{ rewrite Ep. apply footprint_fresh; [lia | exact FI | exact FRG]. }
split.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- repeat split; reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- destruct BND as (_ & B2 & _). exact B2.
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ROr in Hk; injection Hk as <-; discriminate | rewrite (ROo k Hne) in Hk; exact Hk].
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite Hr in Hk; injection Hk as <-; discriminate | rewrite (ROo k Hne); exact Hk].
- intros k rg Hk Hl Hkd. destruct (Nat.eq_dec k r) as [->|Hne].
+ rewrite Hr in Hk. injection Hk as <-. eexists. split; [exact ROr|]. cbn. repeat split; try discriminate. lia.
+ exists rg. rewrite (ROo k Hne). auto with zarith.
- intros k rg' Hk H' Hl. destruct (Nat.eq_dec k r) as [->|Hne]; [eexists; split; [exact Hr | reflexivity] | rewrite (ROo k Hne) in H'; exists rg'; auto].
- unfold N. rewrite ER, length_lupd. lia.
- reflexivity.
- reflexivity.
- intros; reflexivity.
- intros k rg Hk H' _. exfalso. pose proof (region_of_lt _ _ _ H') as LT. rewrite ER, length_lupd in LT. unfold N in Hk. lia.
- exact (proj1 LGX).
- exact (proj2 LGX).
- rewrite MD', m_halted_with, m_vm_lazy_with, m_vm_materialized_with. auto.
- exists (mkRegion RkBrk (PGSZ * pages + PGSZ) [] true). unfold p. cbn [prid poff]. split; [exact ROr|]. cbn. repeat split; try discriminate; try lia.
rewrite PG4, Z.mul_comm. apply Z_mod_mult.
- exact FRESH.
- intros k rg x Hk Hl Hkd Hx Hxr. pose proof (FRESH _ (footprint_region_In A k rg Hk Hkd Hl)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D. lia.
- intros x. right. intros [].
- intros x a [].
- intros x k rg [].
- intros x [].
- intros x [].
- intros x [].
- apply layout_le_refl.
- eexists. exact MD'.
Qed.
End j.
Section s.
Variable md3 : Model.
Hypothesis Hbk : st_brk A = BrkNever.
Let h := m_vmmaps md.
Let b := vm_brk h.
Hypothesis Gceil : bv_unsigned b + 2 * PGSZ <= alloc_ceiling.
Hypothesis Gfree : region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (2 * PGSZ)) = true.
Hypothesis VM3 : vm_maps (m_vmmaps md3) = (b, w64 (2 * PGSZ)) :: vm_maps h \/
vm_maps (m_vmmaps md3) = (w64 (bv_unsigned b + PGSZ), w64 PGSZ) :: vm_maps h.
Hypothesis VN3 : forall lo n, 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + 2 * PGSZ <= bv_unsigned lo) ->
map_contains (vm_noaccess h) lo n = true -> map_contains (vm_noaccess (m_vmmaps md3)) lo n = true.
Hypothesis VNX3 : forall e, In e (vm_noaccess (m_vmmaps md3)) ->
(exists e0, In e0 (vm_noaccess h) /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0) \/
(exists E, In E (vm_maps (m_vmmaps md3)) /\ iv_lo E <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo E + iv_len E /\
bv_unsigned b <= iv_lo E /\ iv_lo E + iv_len E <= bv_unsigned b + 2 * PGSZ).
Hypothesis VR3 : vm_reserved (m_vmmaps md3) = vm_reserved h.
Hypothesis VS3 : vm_start_brk (m_vmmaps md3) = vm_start_brk h.
Hypothesis VB3 : bv_unsigned (vm_brk (m_vmmaps md3)) = bv_unsigned b + 2 * PGSZ.
Hypothesis VL3 : vm_limit (m_vmmaps md3) = vm_limit h.
Hypothesis VT3 : alloc_top (m_vmmaps md3) = alloc_top h.
Hypothesis MD3 : m_halted md3 = None /\ m_vm_lazy md3 = [] /\ m_vm_materialized md3 = [].
Hypothesis MDW3 : exists vm', md3 = with_vmmaps vm' md.
Let p := SP N PGSZ.
Let L' := Lset L A (bv_unsigned b).
Definition sBN : astate := brk2_st A0.
Lemma sBN_open : open_st p sBN = open_st (SP (length (st_regions A)) PGSZ) (brk2_st A0).
Proof. reflexivity. Qed.
Theorem open_BN : open_ctx sBN p L' md3 (fun x => bv_unsigned b <= x < bv_unsigned b + 2 * PGSZ).
Proof.
clear Gceil.
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range b) as Ub.
pose proof (lg_brk0 _ _ _ _ LG) as (B1 & B2 & B3 & B4 & B5).
pose proof (lg_brk _ _ _ _ LG) as HB. rewrite Hbk in HB. change (bv_unsigned b = ly_brk0 L) in HB.
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (ER : st_regions sBN = st_regions A ++ [mkRegion RkBrk (2 * PGSZ) [] true]) by reflexivity.
pose proof (fun k => region_of_new A sBN _ k ER) as RO. cbn beta in RO. fold N in RO.
assert (RON : region_of sBN N = Some (mkRegion RkBrk (2 * PGSZ) [] true)) by (rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl; reflexivity).
assert (ROo : forall k, (k < N)%nat -> region_of sBN k = region_of A k) by (intros k Hk; rewrite RO, (proj2 (Nat.ltb_lt _ _) Hk); reflexivity).
assert (ROhi : forall k rg, region_of sBN k = Some rg -> (k < N)%nat /\ region_of A k = Some rg \/ k = N /\ rg = mkRegion RkBrk (2 * PGSZ) [] true).
{ intros k rg Hk. rewrite RO in Hk. destruct (Nat.ltb_spec k N); [left; auto|]. destruct (Nat.eqb_spec k N); [injection Hk as <-; right; auto | discriminate]. }
assert (LGX : ledger_ok B L' sBN md3 /\ ledger_x L' sBN md3).
{ destruct MD3 as (_ & ML3 & MM3). exact (ledger_new_brk B L A md LG LX NN sBN md3 Hbk Gfree ER eq_refl VM3 VN3 VNX3 VR3 VS3 VB3 VL3 VT3 ML3 MM3). }
pose proof (fresh_region L A md LX b (2 * PGSZ) ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FRG.
pose proof (fresh_img B L A md LG b (2 * PGSZ) ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FI.
assert (Ep : ptr_addr L' p = bv_unsigned b + PGSZ).
{ unfold p, ptr_addr. cbn [loc_addr]. change (ly_reg L' N) with (ly_reg (Lset L A (bv_unsigned b)) (length (st_regions A))). rewrite Lset_new. reflexivity. }
assert (FRESH8 : forall e, In e (footprint A) -> ranges_disjoint (bv_unsigned b, 2 * PGSZ) (crange L e)).
{ apply footprint_fresh; [lia | exact FI | exact FRG]. }
assert (FRESH : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L' p, PGSZ) (crange L e)).
{ intros e He. pose proof (FRESH8 e He) as D. rewrite Ep. unfold ranges_disjoint in *. cbn [fst snd] in *. lia. }
assert (L'reg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r) by (intros r Hr; unfold L'; apply Lset_lt; exact Hr).
split.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- repeat split; reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- destruct BND as (_ & B2' & _). exact B2'.
- intros k rg Hk Hl Hkd. destruct (ROhi k rg Hk) as [[_ H]|[-> ->]]; [exact H | discriminate].
- intros k rg Hk Hl Hkd. rewrite (ROo k (region_of_lt _ _ _ Hk)). exact Hk.
- intros k rg Hk Hl Hkd. exists rg. rewrite (ROo k (region_of_lt _ _ _ Hk)). auto with zarith.
- intros k rg' Hk H' Hl. rewrite (ROo k Hk) in H'. exists rg'. auto.
- unfold N. rewrite ER, length_app. lia.
- reflexivity.
- reflexivity.
- exact L'reg.
- intros k rg Hk H' _. destruct (ROhi k rg H') as [[LT _]|[-> _]]; [unfold N in Hk; lia|]. unfold L'. rewrite Lset_new. rewrite HB. exact B1.
- exact (proj1 LGX).
- exact (proj2 LGX).
- exact MD3.
- exists (mkRegion RkBrk (2 * PGSZ) [] true). unfold p. cbn [prid poff]. split; [exact RON|]. cbn. repeat split; try discriminate; lia.
- exact FRESH.
- intros k rg x Hk Hl Hkd Hx Hxr. pose proof (FRESH _ (footprint_region_In A k rg Hk Hkd Hl)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D. lia.
- intros x. lia.
- intros x a Hx Ha Hxa. pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas a Ha) as (r' & o' & rg' & -> & Ao1 & Ao2 & Ar & Al & Alen & Akind).
apply (FRG r' rg' x Ar Al); [| exact Hx]. unfold ptr_addr in Hxa. cbn in Hxa. unfold reg_lo. destruct (rg_kind rg'); [ | | destruct Akind]; lia.
- intros x k rg Hx Hk Hl Hkd Hxr. apply (FRG k rg x Hk Hl); [| exact Hx]. unfold reg_lo. rewrite Hkd. lia.
- intros x Hx Hi. exact (FI x Hi Hx).
- intros x Hx Hc. apply (FI x); [| exact Hx]. apply (so_ctx_img _ (mid_syms _ _ _ _ _ MID)). exact Hc.
- intros x Hx. pose proof (O_fields X R U L A HI sBN p L' eq_refl eq_refl eq_refl ltac:(repeat split; reflexivity) eq_refl eq_refl ltac:(unfold N; rewrite ER, length_app; lia) eq_refl L'reg FRESH) as OF.
destruct OF as (_ & ERg & _). split.
+ exists N, (mkRegion RkBrk (2 * PGSZ) [] true). unfold region_of. rewrite ERg. fold (region_of sBN N). rewrite RON.
unfold L'. rewrite Lset_new. cbn. repeat split; try discriminate; lia.
+ intros (k & rg & Hk & Hl & Hkd & Hxr). unfold region_of in Hk. rewrite ERg in Hk. fold (region_of sBN k) in Hk.
destruct (ROhi k rg Hk) as [[LT HkA]|[-> ->]]; [| discriminate].
rewrite (L'reg k LT) in Hxr. apply (FRG k rg x HkA Hl); [| exact Hx]. unfold reg_lo. rewrite Hkd. lia.
- unfold layout_le, L'. cbn. repeat split. exact L'reg.
- exact MDW3.
Qed.
End s.
Section u.
Variables (Xs : astate) (a : word).
Hypothesis LXs : like_A0 A Xs.
Hypothesis Haac : st_avail_meta_area_count A = 0.
Let len := Z.shiftl 2 (st_meta_alloc_shift A) * PGSZ.
Hypothesis PL : place_ok (Z_to_bv 64 0) md a len = true.
Let L' := Lset L A (bv_unsigned a).
Let NX := length (st_regions Xs).
Let p := SP NX PGSZ.
Definition sV : astate :=
set_regions (lupd (st_regions (resv_st Xs)) (prid p)
(let rg := nth (prid p) (st_regions (resv_st Xs)) (mkRegion RkMap 0 [] false) in
mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg))) (resv_st Xs).
Definition mdV1 : Model := mmap_none_model a (Z_to_bv 64 len) md.
Definition mdV : Model := mprotect_model (w64 (bv_unsigned a + PGSZ)) (w64 PGSZ) mdV1.
Lemma sV_open : openR_st (resv_st Xs) = open_st p sV.
Proof. reflexivity. Qed.
Lemma ledger_V1 : ledger_ok B L' (resv_st Xs) mdV1 /\ ledger_x L' (resv_st Xs) mdV1.
Proof.
pose proof LXs as (ER & EAr & EMt & EB & Ein & CR & Efh & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama).
pose proof (len_facts B L A mem md BND MID a PL) as (Hlen & Hlmod & Hceil & Ha0 & Hal & RF & Hsh40).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3).
assert (ER1 : st_regions (resv_st Xs) = st_regions A ++ [mkRegion RkMetaRes len [] true]).
{ unfold resv_st. cbn. rewrite ER, Esh. reflexivity. }
destruct (ledger_like B L A mem md MID Xs LXs) as [LGs LXs'].
assert (NNs : forall k rg, region_of Xs k = Some rg -> 0 <= rg_len rg) by (intros k rg; unfold region_of; rewrite ER; apply NN).
destruct (ledger_new_resv B L Xs md LGs LXs' NNs (conj M1 (conj M2 M3)) (resv_st Xs) a len Hlen Hlmod PL ltac:(rewrite ER; exact ER1) ltac:(unfold resv_st; cbn; reflexivity)) as [G1 G2].
{ intros r pg Hb. pose proof (inv_areas HI) as (_&_&_&_&_&_&Hbrk&_). destruct EB as [EB'|EB']; rewrite EB' in Hb; [|discriminate].
rewrite Hb in Hbrk. destruct Hbrk as (_ & rg & Hrg & _). rewrite ER. exact (region_of_lt _ _ _ Hrg). }
assert (ELs : Lset L Xs (bv_unsigned a) = L') by (unfold L', Lset; rewrite ER; reflexivity). rewrite ELs in G1, G2. exact (conj G1 G2).
Qed.
Theorem open_V : open_ctx sV p L' mdV (fun x => bv_unsigned a <= x < bv_unsigned a + len).
Proof.
pose proof LXs as (ER & EAr & EMt & EB & Ein & CR & Efh & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama).
pose proof (len_facts B L A mem md BND MID a PL) as (Hlen & Hlmod & Hceil & Ha0 & Hal & RF & Hsh40).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
pose proof BND as (_ & Bsh & _).
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (ENX : NX = N) by (unfold NX, N; rewrite ER; reflexivity).
assert (Hlen2 : 2 * PGSZ <= len).
{ unfold len. rewrite Z.shiftl_mul_pow2 by lia. assert (1 <= 2 ^ st_meta_alloc_shift A) by (apply Z.pow_le_mono_r with (a := 0) in Bsh || pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift A)); lia). nia. }
set (R1 := resv_st Xs).
assert (ER1 : st_regions R1 = st_regions A ++ [mkRegion RkMetaRes len [] true]).
{ unfold R1, resv_st. cbn. rewrite ER, Esh. reflexivity. }
assert (ER3 : st_regions sV = st_regions A ++ [mkRegion RkMetaRes len [PGSZ] true]).
{ unfold sV. cbn [st_regions set_regions prid poff p]. fold R1. rewrite ER1.
replace NX with (length (st_regions A)) by (unfold NX; rewrite ER; reflexivity).
rewrite nth_app_last, lupd_app_last. reflexivity. }
pose proof (fun k => region_of_new A sV _ k ER3) as RO. cbn beta in RO. fold N in RO.
pose proof (fun k => region_of_new A R1 _ k ER1) as RO1. cbn beta in RO1. fold N in RO1.
assert (RON : region_of sV N = Some (mkRegion RkMetaRes len [PGSZ] true)) by (rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl; reflexivity).
assert (ROo : forall k, (k < N)%nat -> region_of sV k = region_of A k) by (intros k Hk; rewrite RO, (proj2 (Nat.ltb_lt _ _) Hk); reflexivity).
assert (ROhi : forall k rg, region_of sV k = Some rg -> (k < N)%nat /\ region_of A k = Some rg \/ k = N /\ rg = mkRegion RkMetaRes len [PGSZ] true).
{ intros k rg Hk. rewrite RO in Hk. destruct (Nat.ltb_spec k N); [left; auto|]. destruct (Nat.eqb_spec k N); [injection Hk as <-; right; auto | discriminate]. }
assert (L'reg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r) by (intros r Hr; unfold L'; apply Lset_lt; exact Hr).
assert (L'N : ly_reg L' N = bv_unsigned a) by (unfold L'; apply Lset_new).
destruct (ledger_like B L A mem md MID Xs LXs) as [LGs LXs'].
assert (NNs : forall k rg, region_of Xs k = Some rg -> 0 <= rg_len rg) by (intros k rg; unfold region_of; rewrite ER; apply NN).
assert (LGX1 : ledger_ok B L' R1 mdV1 /\ ledger_x L' R1 mdV1).
{ destruct (ledger_new_resv B L Xs md LGs LXs' NNs (conj M1 (conj M2 M3)) R1 a len Hlen Hlmod PL ltac:(rewrite ER; exact ER1) ltac:(unfold R1, resv_st; cbn; reflexivity)) as [G1 G2].
{ intros r pg Hb. pose proof (inv_areas HI) as (_&_&_&_&_&_&Hbrk&_). destruct EB as [EB'|EB']; rewrite EB' in Hb; [|discriminate].
rewrite Hb in Hbrk. destruct Hbrk as (_ & rg & Hrg & _). rewrite ER. exact (region_of_lt _ _ _ Hrg). }
assert (ELs : Lset L Xs (bv_unsigned a) = L') by (unfold L', Lset; rewrite ER; reflexivity). rewrite ELs in G1, G2. exact (conj G1 G2). }
assert (MDV1 : m_halted mdV1 = None /\ m_vm_lazy mdV1 = [] /\ m_vm_materialized mdV1 = []).
{ unfold mdV1, mmap_none_model. rewrite m_halted_with, m_vm_lazy_with, m_vm_materialized_with. auto. }
assert (R1N : region_of R1 N = Some (mkRegion RkMetaRes len [] true)) by (rewrite RO1, Nat.ltb_irrefl, Nat.eqb_refl; reflexivity).
assert (LGX : ledger_ok B L' sV mdV /\ ledger_x L' sV mdV).
{ unfold mdV. rewrite <- L'N.
apply (ledger_mprotect B L' R1 mdV1 (proj1 LGX1) (proj2 LGX1) MDV1 sV N len [] PGSZ R1N); try lia.
- rewrite PG4. reflexivity.
- intros [].
- rewrite ER3, ER1. cbn [app]. symmetry. apply lupd_app_last.
- unfold sV, R1. reflexivity. }
pose proof (fresh_region L A md LX a len Hlen Ha0 ltac:(lia) RF) as FRG.
pose proof (fresh_img B L A md LG a len Hlen Ha0 ltac:(lia) RF) as FI.
assert (Ep : ptr_addr L' p = bv_unsigned a + PGSZ) by (unfold p, ptr_addr; cbn [loc_addr]; rewrite ENX, L'N; reflexivity).
assert (FRESHL : forall e, In e (footprint A) -> ranges_disjoint (bv_unsigned a, len) (crange L e)).
{ apply footprint_fresh; [lia | exact FI | exact FRG]. }
assert (FRESH : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L' p, PGSZ) (crange L e)).
{ intros e He. pose proof (FRESHL e He) as D. rewrite Ep. unfold ranges_disjoint in *. cbn [fst snd] in *. lia. }
split.
- unfold sV. cbn. exact EAr.
- unfold sV. cbn. exact EMt.
- reflexivity.
- unfold sV. cbn. exact Ein.
- unfold sV, resv_st, ctx_rest_same in *. cbn. exact CR.
- unfold sV. cbn. exact Ehd.
- unfold sV. cbn. exact Etl.
- unfold sV. cbn. exact Efh.
- unfold sV. cbn. rewrite Esh. lia.
- intros k rg Hk Hl Hkd. destruct (ROhi k rg Hk) as [[_ H]|[-> ->]]; [exact H | discriminate].
- intros k rg Hk Hl Hkd. rewrite (ROo k (region_of_lt _ _ _ Hk)). exact Hk.
- intros k rg Hk Hl Hkd. exists rg. rewrite (ROo k (region_of_lt _ _ _ Hk)). auto with zarith.
- intros k rg' Hk H' Hl. rewrite (ROo k Hk) in H'. exists rg'. auto.
- unfold N. rewrite ER3, length_app. lia.
- reflexivity.
- reflexivity.
- exact L'reg.
- intros k rg Hk H' _. destruct (ROhi k rg H') as [[LT _]|[-> _]]; [unfold N in Hk; lia|]. rewrite L'N. exact Hal.
- exact (proj1 LGX).
- exact (proj2 LGX).
- unfold mdV, mprotect_model, mprotect_model_next. rewrite m_halted_with, m_vm_lazy_with, m_vm_materialized_with. exact MDV1.
- exists (mkRegion RkMetaRes len [PGSZ] true). unfold p. cbn [prid poff]. rewrite ENX. split; [exact RON|]. cbn. repeat split; try discriminate; lia.
- exact FRESH.
- intros k rg x Hk Hl Hkd Hx Hxr. pose proof (FRESH _ (footprint_region_In A k rg Hk Hkd Hl)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D. lia.
- intros x. lia.
- intros x ar Hx Ha Hxa. pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas ar Ha) as (r' & o' & rg' & -> & Ao1 & Ao2 & Ar & Al & Alen & Akind).
apply (FRG r' rg' x Ar Al); [| exact Hx]. unfold ptr_addr in Hxa. cbn in Hxa. unfold reg_lo. destruct (rg_kind rg'); [ | | destruct Akind]; lia.
- intros x k rg Hx Hk Hl Hkd Hxr. apply (FRG k rg x Hk Hl); [| exact Hx]. unfold reg_lo. rewrite Hkd. lia.
- intros x Hx Hi. exact (FI x Hi Hx).
- intros x Hx Hc. apply (FI x); [| exact Hx]. apply (so_ctx_img _ (mid_syms _ _ _ _ _ MID)). exact Hc.
- intros x Hx.
assert (ERg : st_regions (take_st (open_st p sV)) = st_regions sV) by reflexivity.
split.
+ exists N, (mkRegion RkMetaRes len [PGSZ] true). unfold region_of. rewrite ERg. fold (region_of sV N). rewrite RON, L'N. cbn. repeat split; try discriminate; lia.
+ intros (k & rg & Hk & Hl & Hkd & Hxr). unfold region_of in Hk. rewrite ERg in Hk. fold (region_of sV k) in Hk.
destruct (ROhi k rg Hk) as [[LT HkA]|[-> ->]]; [| discriminate].
rewrite (L'reg k LT) in Hxr. apply (FRG k rg x HkA Hl); [| exact Hx]. unfold reg_lo. rewrite Hkd. lia.
- unfold layout_le, L'. cbn. repeat split. exact L'reg.
- eexists. unfold mdV, mdV1, mprotect_model, mprotect_model_next, mmap_none_model. rewrite with_vmmaps_twice'. reflexivity.
Qed.
End u.
End f.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
