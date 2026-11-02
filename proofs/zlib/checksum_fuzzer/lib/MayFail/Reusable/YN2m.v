(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2m.v, with its module paths changed. *)
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
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition onum (L : layout) (o : option sptr) : Z := match o with Some p => ptr_addr L p | None => 0 end.
Lemma sval_num_optr : forall L o, sval_num L (optr o) = onum L o.
Proof. intros L [p|]; reflexivity. Qed.
Definition ctx_at (B : malloc_syms) (mem : word -> option byte) (off : Z) (w : nat) (v : Z) : Prop :=
forall k, (k < w)%nat -> mbyte (ms_segs B) mem (ms_ctx B + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k)).
Lemma nil_or_not {T} : forall l : list T, l = [] \/ l <> [].
Proof. intros [|x l]; [left; reflexivity | right; discriminate]. Qed.
Section t.
Variable B : malloc_syms.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis XC : Xclean X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis MID : midrep B L A mem md.
Let A0 := set_init_done true A.
Let N := length (st_regions A).
Let SO : syms_ok B := mid_syms _ _ _ _ _ MID.
Let LG : ledger_ok B L A md := mid_ledger _ _ _ _ _ MID.
Let LX : ledger_x L A md := mid_ledgerx _ _ _ _ _ MID.
Let MR : memrep B L A mem := mid_mem _ _ _ _ _ MID.
Let HI0 : Inv X R U A0 := Inv_set_init_done X R U A HI.
Let NN : forall k rg, region_of A k = Some rg -> 0 <= rg_len rg := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HI)))))))).
Lemma ctx_cell_of_at : forall L' mem' off w v,
ly_ctx L' = ms_ctx B -> ctx_at B mem' off w (sval_num L' v) -> (forall z, v <> VLo5 z) ->
cell_mem B L' mem' (MCell (LCtx off) w v).
Proof.
intros L' mem' off w v Hc H Hv. unfold cell_mem. cbn [mc_loc mc_w mc_val loc_addr]. rewrite Hc.
destruct v as [z|p|z|]; try exact H. exfalso. exact (Hv z eq_refl).
Qed.
Definition am_scratch (sp : Z) (x : Z) : Prop := (sp - AM_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4).
Definition ctxW (x : Z) : Prop :=
(ms_ctx B <= x < ms_ctx B + 12) \/ (ms_ctx B + 16 <= x < ms_ctx B + 80) \/ (ms_ctx B + 920 <= x < ms_ctx B + 928).
Lemma areas_off_img : forall a x, In a (st_areas A) -> ptr_addr L a <= x < ptr_addr L a + PGSZ -> ~ in_img B x /\ 4096 <= x < alloc_ceiling.
Proof.
intros a x Ha Hx. pose proof (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & Ea & Ho & Hlo & Hr & Hl & Hlen & _). rewrite Ea in Hx.
pose proof (lg_placed _ _ _ _ LG r rg Hr Hl) as (_ & P1 & P2 & Pimg). unfold ptr_addr in Hx. cbn in Hx.
split; [apply Pimg; unfold PGSZ in *; lia | unfold PGSZ in *; lia].
Qed.
Lemma area_nonmap : forall A' L' a x,
In a (st_areas A) -> ptr_addr L a <= x < ptr_addr L a + PGSZ ->
(forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
exists rg', region_of A' k = Some rg' /\ rg_live rg' = true /\ rg_kind rg' <> RkMap /\ rg_len rg <= rg_len rg') ->
(forall k rg, region_of A' k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of A k = Some rg) ->
(forall k, (k < N)%nat -> ly_reg L' k = ly_reg L k) ->
in_nonmap_region L' A' x.
Proof.
intros A' L' a x Ha Hx KEEP BACK EL. pose proof (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & Ea & Ho & Hlo & Hr & Hl & Hlen & Hk). rewrite Ea in Hx.
assert (Hkind : rg_kind rg <> RkMap) by (intros E; rewrite E in Hk; exact Hk).
unfold ptr_addr in Hx. cbn in Hx. split.
- destruct (KEEP r rg Hr Hl Hkind) as (rg' & Hr' & Hl' & Hk' & Hlen').
exists r, rg'. rewrite (EL r (region_of_lt _ _ _ Hr)). repeat split; try assumption; unfold PGSZ in *; lia.
- intros (k & rg2 & Hk2 & Hl2 & Hkd2 & Hx2). pose proof (BACK k rg2 Hk2 Hl2 Hkd2) as HkA.
rewrite (EL k (region_of_lt _ _ _ HkA)) in Hx2.
assert (Hne : r <> k) by (intros ->; rewrite HkA in Hr; injection Hr as ->; exact (Hkind Hkd2)).
pose proof (lx_regs _ _ _ LX r k rg rg2 Hne Hr HkA Hl Hl2) as D.
unfold reg_lo, ranges_disjoint in D. rewrite Hkd2 in D. cbn [fst snd] in D.
destruct (rg_kind rg); [ | | exact (Hkind eq_refl)]; unfold PGSZ in *; lia.
Qed.
Lemma areas_count_bound : Z.of_nat (length (st_areas A)) + 1 < 2 ^ 36.
Proof.
pose proof (inv_areas HI) as (ND & Hareas & _). pose proof (proj1 alloc_ceiling_val) as AC.
set (f := fun a => Z.to_nat (ptr_addr L a / 4096)).
assert (INJ : forall a1 a2, In a1 (st_areas A) -> In a2 (st_areas A) -> f a1 = f a2 -> a1 = a2).
{ intros a1 a2 H1 H2 Ef. destruct (sptr_eq_dec a1 a2) as [E|Hne]; [exact E|]. exfalso.
pose proof (areas_pages_disjoint B L A mem md MID a1 a2 H1 H2 Hne) as D.
destruct (areas_off_img a1 (ptr_addr L a1) H1 ltac:(unfold PGSZ; lia)) as [_ R1].
destruct (areas_off_img a2 (ptr_addr L a2) H2 ltac:(unfold PGSZ; lia)) as [_ R2].
unfold f in Ef. unfold PGSZ in D.
assert (ptr_addr L a1 / 4096 = ptr_addr L a2 / 4096) by lia.
pose proof (Z.div_mod (ptr_addr L a1) 4096 ltac:(lia)). pose proof (Z.div_mod (ptr_addr L a2) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (ptr_addr L a1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (ptr_addr L a2) 4096 ltac:(lia)). lia. }
assert (ACE : alloc_ceiling = 4096 * (alloc_ceiling / 4096)).
{ apply (proj2 (Z.div_exact alloc_ceiling 4096 ltac:(lia))). exact (proj2 alloc_ceiling_val). }
assert (BOUND : forall a, In a (st_areas A) -> (f a < Z.to_nat (alloc_ceiling / 4096))%nat).
{ intros a Ha. destruct (areas_off_img a (ptr_addr L a) Ha ltac:(unfold PGSZ; lia)) as [_ R1]. unfold f.
apply Z2Nat.inj_lt; [apply Z.div_pos; lia | apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia|].
rewrite <- ACE. lia. }
assert (ND' : NoDup (map f (st_areas A))).
{ assert (GEN : forall l, NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l)).
{ induction l as [|a l IH]; intros NDl INJl; cbn; [constructor|].
inversion NDl; subst. constructor.
- intros Hin. apply in_map_iff in Hin as (a' & Ef & Ha'). apply H1.
rewrite <- (INJl a' a ltac:(right; exact Ha') ltac:(left; reflexivity) Ef). exact Ha'.
- apply IH; [exact H2 | intros x y Hx Hy; apply INJl; right; assumption]. }
apply GEN; [exact ND | exact INJ]. }
assert (INCL : incl (map f (st_areas A)) (seq 0 (Z.to_nat (alloc_ceiling / 4096)))).
{ intros y Hy. apply in_map_iff in Hy as (a & <- & Ha). apply in_seq. split; [lia | apply BOUND; exact Ha]. }
pose proof (NoDup_incl_length ND' INCL) as LEN. rewrite length_map, length_seq in LEN.
assert (HQ : alloc_ceiling / 4096 <= 34359736320) by (apply Z.div_le_upper_bound; lia).
assert (HQ0 : 0 <= alloc_ceiling / 4096) by (apply Z.div_pos; lia).
rewrite <- (Z2Nat.id (alloc_ceiling / 4096)) in HQ by exact HQ0.
assert (Z.of_nat (length (st_areas A)) <= 34359736320) by lia. lia.
Qed.
Hypothesis ENC : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Hypothesis ENS : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x.
Hypothesis ERRIMG : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Hypothesis SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Definition amav (s : astate) : sval :=
if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s).
Definition brkv (s : astate) : sval :=
match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end.
Definition amv (s : astate) : sval := match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end.
Definition ctx11 (L' : layout) (mem' : word -> option byte) (s : astate) : Prop :=
ctx_at B mem' 0 8 (sval_num L' (if st_init_done s then VSec else VZ 0)) /\
ctx_at B mem' 8 4 (if st_init_done s then 1 else 0) /\
ctx_at B mem' 16 8 (onum L' (st_free_meta_head s)) /\
ctx_at B mem' 24 8 (sval_num L' (amv s)) /\
ctx_at B mem' 32 8 (st_avail_meta_count s) /\
ctx_at B mem' 40 8 (st_avail_meta_area_count s) /\
ctx_at B mem' 48 8 (st_meta_alloc_shift s) /\
ctx_at B mem' 56 8 (onum L' (st_area_head s)) /\
ctx_at B mem' 64 8 (onum L' (st_area_tail s)) /\
ctx_at B mem' 72 8 (sval_num L' (amav s)) /\
ctx_at B mem' 920 8 (sval_num L' (brkv s)).
Definition ctx_rest_same (s : astate) : Prop :=
st_mmap_counter s = st_mmap_counter A /\ st_seq s = st_seq A /\ st_active s = st_active A /\
st_usage s = st_usage A /\ st_unmap_seq s = st_unmap_seq A /\ st_bounces s = st_bounces A.
Lemma CTX_std : forall L' mem' A' (W : Z -> Prop),
ly_ctx L' = ms_ctx B -> ctx11 L' mem' A' -> ctx_rest_same A' ->
(forall x, W x -> ms_ctx B <= x < ms_ctx B + CTX_SIZE -> ctxW x) ->
forall c, In c (ctx_cells A') ->
(In c (ctx_cells A) /\ forall k, (k < mc_w c)%nat -> ~ W (ms_ctx B + (match mc_loc c with LCtx o => o | _ => 0 end) + Z.of_nat k)) \/
cell_mem B L' mem' c.
Proof.
intros L' mem' A' W HLc (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10) (E1 & E2 & E3 & E4 & E5 & E6) WC c Hc.
assert (NW : forall off (w : nat) k, (k < w)%nat -> 0 <= off -> off + Z.of_nat w <= CTX_SIZE ->
~ ctxW (ms_ctx B + off + Z.of_nat k) -> ~ W (ms_ctx B + off + Z.of_nat k)).
{ intros off w k Hk Ho1 Ho2 Hn HW. apply Hn. apply WC; [exact HW|]. unfold CTX_SIZE in *. lia. }
destruct (In_ctx_cells_cases 0 A' c Hc) as [H13 | [(k & Hk & ->) | [(k & Hk & ->) | [(k & Hk & ->) | (k & Hk & ->)]]]].
- cbn [In] in H13.
Ltac cellat HLc C := right; apply (ctx_cell_of_at _ _ _ _ _ HLc); [ | intros z; try discriminate].
destruct H13 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]].
+ cellat HLc C0; [exact C0 | destruct (st_init_done A'); discriminate].
+ cellat HLc C1. cbn [sval_num]. exact C1.
+   left. rewrite E1. split; [unfold ctx_cells; apply in_app_iff; left; cbn; tauto|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW 12 4%nat j Hj); [lia | unfold CTX_SIZE; lia |]. unfold ctxW, CTX_mmap_counter. lia.
+ cellat HLc C2; [rewrite sval_num_optr; exact C2 | destruct (st_free_meta_head A'); discriminate].
+ cellat HLc C3; [unfold amv in C3; exact C3 | destruct (st_areas A'); discriminate].
+ cellat HLc C4. cbn [sval_num]. exact C4.
+ cellat HLc C5. cbn [sval_num]. exact C5.
+ cellat HLc C6. cbn [sval_num]. exact C6.
+ cellat HLc C7; [rewrite sval_num_optr; exact C7 | destruct (st_area_head A'); discriminate].
+ cellat HLc C8; [rewrite sval_num_optr; exact C8 | destruct (st_area_tail A'); discriminate].
+ cellat HLc C9; [unfold amav in C9; exact C9 | destruct (_ && _); discriminate].
+   left. rewrite E2. split; [unfold ctx_cells; apply in_app_iff; left; cbn; tauto|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW 912 1%nat j Hj); [lia | unfold CTX_SIZE; lia |]. unfold ctxW, CTX_seq. lia.
+ cellat HLc C10; [unfold brkv in C10; exact C10 | destruct (st_brk A'); discriminate].
- left. rewrite E3. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW (CTX_active + 8 * Z.of_nat k) 8%nat j Hj); unfold CTX_active, CTX_SIZE, ctxW; lia.
- left. rewrite E4. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW (CTX_usage + 8 * Z.of_nat k) 8%nat j Hj); unfold CTX_usage, CTX_SIZE, ctxW; lia.
- left. rewrite E5. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW (CTX_unmap_seq + Z.of_nat k) 1%nat j Hj); unfold CTX_unmap_seq, CTX_SIZE, ctxW; lia.
- left. rewrite E6. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_w mc_loc] in *. apply (NW (CTX_bounces + Z.of_nat k) 1%nat j Hj); unfold CTX_bounces, CTX_SIZE, ctxW; lia.
Qed.
Lemma Wdec_interval : forall lo hi x, (lo <= x < hi) \/ ~ (lo <= x < hi).
Proof. intros. lia. Qed.
Lemma scratch_not_region : forall sp x k rg, alloc_ceiling + AM_STACK <= sp ->
am_scratch sp x -> region_of A k = Some rg -> rg_live rg = true -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg).
Proof.
intros sp x k rg Hsp [Hs|Hs] Hk Hl Hx.
- pose proof (lg_placed _ _ _ _ LG k rg Hk Hl) as (_ & _ & P & _). unfold AM_STACK in *. lia.
- pose proof (lg_placed _ _ _ _ LG k rg Hk Hl) as (_ & _ & _ & P). exact (P x Hx (ERRIMG x Hs)).
Qed.
Lemma ctxW_not_region : forall x k rg, ctxW x -> region_of A k = Some rg -> rg_live rg = true -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg).
Proof.
intros x k rg Hc Hk Hl Hx. pose proof (lg_placed _ _ _ _ LG k rg Hk Hl) as (_ & _ & _ & P).
apply (P x Hx). apply (so_ctx_img _ SO). unfold ctxW, CTX_SIZE in *. lia.
Qed.
Lemma scratch_not_area : forall sp x a, alloc_ceiling + AM_STACK <= sp ->
am_scratch sp x -> In a (st_areas A) -> ~ (ptr_addr L a <= x < ptr_addr L a + PGSZ).
Proof.
intros sp x a Hsp Hs Ha Hx. destruct (areas_off_img a x Ha Hx) as [Hi Hr].
destruct Hs as [Hs|Hs]; [unfold AM_STACK in *; lia | exact (Hi (ERRIMG x Hs))].
Qed.
Lemma ctxW_not_area : forall x a, ctxW x -> In a (st_areas A) -> ~ (ptr_addr L a <= x < ptr_addr L a + PGSZ).
Proof.
intros x a Hc Ha Hx. destruct (areas_off_img a x Ha Hx) as [Hi Hr]. apply Hi. apply (so_ctx_img _ SO). unfold ctxW, CTX_SIZE in *. lia.
Qed.
Lemma A_init_fields : forall b, st_areas (set_init_done b A) = st_areas A /\ st_regions (set_init_done b A) = st_regions A /\
st_metas (set_init_done b A) = st_metas A /\ st_brk (set_init_done b A) = st_brk A.
Proof. intros b. repeat split; reflexivity. Qed.
Lemma bounded_keep : forall A', st_usage A' = st_usage A -> st_meta_alloc_shift A' <= st_meta_alloc_shift A + 0 ->
0 <= st_meta_alloc_shift A' -> Z.of_nat (length (st_areas A')) <= Z.of_nat (length (st_areas A)) + 1 -> bounded A'.
Proof.
intros A' EU ES ES0 EA. destruct BND as (B1 & B2 & B3). pose proof areas_count_bound. unfold bounded, usage_of in *. rewrite EU. repeat split; try apply B1; lia.
Qed.
Section u.
Hypothesis Hamc : 0 < st_avail_meta_count A.
Let m := st_avail_meta A.
Let A' := take_st A0.
Lemma C_facts : ~ In m (keys A) /\ Inv (m :: X) R U A' /\ st_areas A <> [] /\
(exists k, 0 <= k < METAS_PER_AREA /\ m = slot_of (last (st_areas A) (SP 0%nat 0)) k) /\ In (last (st_areas A) (SP 0%nat 0)) (st_areas A).
Proof.
destruct (take_slot_Inv X R U A0 HI0 Hamc) as (Hfresh & _ & HI' & _).
pose proof (inv_keys HI) as (ND & KP & Hnil & Hav & Hcnt).
assert (Hne : st_areas A <> []) by (intros E; pose proof (Hnil E); lia).
split; [exact Hfresh|]. split; [exact HI'|]. split; [exact Hne|]. split.
- exists (METAS_PER_AREA - st_avail_meta_count A). split; [lia|]. unfold m, slot_of. apply Hav. exact Hne.
- apply In_last. exact Hne.
Qed.
Lemma C_MT : forall q, MT A' q = if sptr_eqb q m then Some MRaw else MT A q.
Proof.
intros q. unfold A', take_st, A0. destruct (sptr_eqb q m) eqn:E.
- apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
- rewrite MT_upd_other; [reflexivity|]. intros ->. rewrite sptr_eqb_refl in E. discriminate.
Qed.
Lemma C_used : used_metas A' = used_metas A.
Proof.
destruct C_facts as (Hfresh & HI' & _).
apply (used_metas_same A A' [m]); [exact (proj1 (inv_keys HI')) | |].
- unfold A', take_st, A0. rewrite keys_upd_notIn; [reflexivity | exact Hfresh].
- intros g am. rewrite C_MT. destruct (sptr_eqb g m) eqn:E; [|tauto].
apply sptr_eqb_eq in E. subst g. split; [discriminate|]. intros H. exfalso. apply Hfresh. exact (MT_Some_In_keys _ _ _ H).
Qed.
Definition WC (sp : Z) (x : Z) : Prop := am_scratch sp x \/ ctxW x \/ (ptr_addr L m <= x < ptr_addr L m + 16).
Theorem post_C : forall sp mem' md',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WC sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 L mem' A' ->
(forall k, (k < 16)%nat -> mbyte (ms_segs B) mem' (ptr_addr L m + Z.of_nat k) = Some (Z_to_bv 8 0)) ->
(forall x, ptr_addr L m <= x < ptr_addr L m + 16 -> present mem' x) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_halted md' = m_halted md ->
midrep B L A' mem' md' /\ ama_ok A' /\ bounded A' /\ ptr_addr L m <> 0 /\
(forall x, ptr_addr L m <= x < ptr_addr L m + 16 -> in_nonmap_region L A' x).
Proof.
intros sp mem' md' Hsp FR C11 LNK LNKP EV EL EM EH.
destruct C_facts as (Hfresh & HI' & Hne & (kk & Hkk & Em) & Hlast).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3).
assert (RG : forall k, region_of A' k = region_of A k) by (intros k; reflexivity).
assert (EA : st_areas A' = st_areas A ++ []) by (rewrite app_nil_r; reflexivity).
assert (Wdec : forall x, WC sp x \/ ~ WC sp x) by (intros x; unfold WC, am_scratch, ctxW; lia).
assert (INPAGE : forall x, ptr_addr L m <= x < ptr_addr L m + 16 -> ptr_addr L (last (st_areas A) (SP 0%nat 0)) <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + PGSZ).
{ intros x Hx. rewrite Em in Hx. unfold slot_of in Hx. rewrite ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
assert (MEMREP : memrep B L A' mem').
{ refine (memrep_xfer B X R U L L A A' mem mem' md HI XC AMA MID C_used [] EA ltac:(intros; discriminate)
(proj1 (inv_areas HI')) ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto)
eq_refl eq_refl ltac:(intros; reflexivity) (WC sp) Wdec FR _ [m] _ _ _ _ _ _ _ _ _).
- intros x k rg HWx Hk Hl Hkd. destruct HWx as [Hs|[Hc|Hm]].
+ exact (scratch_not_region sp x k rg Hsp Hs Hk Hl).
+ exact (ctxW_not_region x k rg Hc Hk Hl).
+ pose proof (area_nonmap A L _ x Hlast (INPAGE x Hm)
ltac:(intros k0 rg0 H0 L0 K0; exists rg0; auto with zarith) ltac:(intros k0 rg0 H0 _ _; exact H0) ltac:(intros; reflexivity)) as [_ NM].
intros Hx. apply NM. exists k, rg. auto.
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|Hm]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ left. exists m. split; [left; reflexivity | exact Hm].
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|Hm]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ exact (LNKP x Hm).
- intros q [<-|[]]. exists (last (st_areas A) (SP 0%nat 0)), kk. auto.
- intros q [<-|[]]. rewrite C_MT, sptr_eqb_refl.
assert (MTm : MT A m = None) by (apply mlookup_None_iff; exact Hfresh). rewrite MTm.
split; [exact I|]. split; [exact I|]. cbn [lnk_prev lnk_next].
split; (unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros j Hj; rewrite YN03.le_byte_0).
+ change (loc_addr L (LMem (padd m META_prev))) with (ptr_addr L (padd m META_prev)). rewrite ptr_addr_padd. unfold META_prev. rewrite Z.add_0_r. apply LNK. lia.
+ change (loc_addr L (LMem (padd m META_next))) with (ptr_addr L (padd m META_next)). rewrite ptr_addr_padd. unfold META_next.
replace (ptr_addr L m + 8 + Z.of_nat j) with (ptr_addr L m + Z.of_nat (8 + j)) by lia. apply LNK. lia.
- intros a k Ha Hk Hnin. rewrite C_MT. destruct (sptr_eqb (slot_of a k) m) eqn:E; [|reflexivity].
exfalso. apply Hnin. left. symmetry. apply sptr_eqb_eq. exact E.
- intros p Hp. discriminate.
- intros p c Hp. discriminate.
- intros p x Hp. discriminate.
- apply (CTX_std L mem' A' (WC sp) (mid_ctx _ _ _ _ _ MID) C11).
+ repeat split; reflexivity.
+ intros x HWx Hcx. destruct HWx as [Hs|[Hc|Hm]]; [| exact Hc |].
* exfalso. destruct Hs as [Hs|Hs]; [pose proof (so_ctx_hi _ SO); unfold AM_STACK in *; lia | exact (ENC x Hs Hcx)].
* exfalso. destruct (areas_off_img _ x Hlast (INPAGE x Hm)) as [Hi _]. apply Hi. apply (so_ctx_img _ SO). exact Hcx. }
split; [|split; [|split; [|split]]].
- split.
+ exact SO.
+ exact MEMREP.
+ apply (tail_geom_xfer B X R U L L A A' mem md HI XC MID C_used); [intros k rg Hk; rewrite RG; auto | reflexivity | intros; reflexivity].
+ apply (statics_xfer B mem mem' (WC sp) SO (mid_statics _ _ _ _ _ MID) FR).
intros x Hst [Hs|[Hc|Hm]].
* destruct Hs as [Hs|Hs]; [| exact (ENS x Hs Hst)].
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hst)). unfold AM_STACK in *. lia.
* apply (SNC x Hst). unfold ctxW, CTX_SIZE in *. lia.
* destruct (areas_off_img _ x Hlast (INPAGE x Hm)) as [Hi _]. exact (Hi (so_statics_img _ SO x Hst)).
+ destruct (ledger_same B L A md LG LX A' md' eq_refl eq_refl EV EL EM) as [G _]. exact G.
+ destruct (ledger_same B L A md LG LX A' md' eq_refl eq_refl EV EL EM) as [_ G]. exact G.
+ refine (layout_ok_xfer B X R U L L A A' mem md HI MID [] EA ltac:(intros; discriminate)
ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto) eq_refl ltac:(intros; reflexivity) _ _ _ _ _).
* cbn. lia.
* intros; discriminate.
* intros; discriminate.
* intros k rg Hk H'. rewrite RG in H'. pose proof (region_of_lt _ _ _ H'). exfalso. unfold N in *. lia.
* intros k rg' Hk H' Hl. rewrite RG in H'. exists rg'. auto.
+ exact (mid_ctx _ _ _ _ _ MID).
+ exact (mid_sec _ _ _ _ _ MID).
+ rewrite EH, EL, EM. exact (conj M1 (conj M2 M3)).
- unfold ama_ok in *. cbn -[Nat.lt prid]. exact AMA.
- apply bounded_keep; [reflexivity | cbn; lia | destruct BND as (_ & B2 & _); cbn in *; lia | cbn; lia].
- destruct (areas_off_img _ (ptr_addr L m) Hlast (INPAGE (ptr_addr L m) ltac:(lia))) as [_ Hr]. lia.
- intros x Hx. apply (area_nonmap A L _ x Hlast (INPAGE x Hx)); [| intros k0 rg0 H0 _ _; exact H0 | intros; reflexivity].
intros k0 rg0 H0 L0 K0. exists rg0. auto with zarith.
Qed.
End u.
Section a0.
Variable m : sptr.
Hypothesis Hhd : st_free_meta_head A = Some m.
Definition QsD (rest : list sptr) : list sptr := m :: match rest with [] => [] | _ => [hd m rest; last rest m] end.
Definition WD (rest : list sptr) (sp : Z) (x : Z) : Prop := am_scratch sp x \/ ctxW x \/ exists q, In q (QsD rest) /\ ptr_addr L q <= x < ptr_addr L q + 16.
Section b0.
Variables (rest : list sptr) (A1 : astate).
Hypothesis RING : ring_ok (flinks X A0) (Some m) (m :: rest).
Hypothesis MEMS : forall q, In q (m :: rest) -> exists qp qn, MT A0 q = Some (MFree qp qn) /\ memb q X = false.
Hypothesis DP : deq_post A0 m rest (MFree (Some (last rest m)) (Some (hd m rest))) (tt, A1).
Lemma D_facts :
st_areas A1 = st_areas A /\ st_regions A1 = st_regions A /\ st_brk A1 = st_brk A /\ keys A1 = keys A /\
st_init_done A1 = true /\ st_avail_meta A1 = st_avail_meta A /\ st_avail_meta_count A1 = st_avail_meta_count A /\
st_avail_meta_area_count A1 = st_avail_meta_area_count A /\ st_meta_alloc_shift A1 = st_meta_alloc_shift A /\
st_area_head A1 = st_area_head A /\ st_area_tail A1 = st_area_tail A /\ st_avail_meta_areas A1 = st_avail_meta_areas A /\
st_free_meta_head A1 = match rest with [] => None | y :: _ => Some y end /\ ctx_rest_same A1 /\
(forall q, In q (m :: rest) -> In q (keys A)) /\ NoDup (m :: rest).
Proof.
destruct DP as (S1 & S2 & S3 & S4 & S5 & S6). cbn [snd] in *.
destruct S1 as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
cbn in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17.
repeat (split; [first [assumption | reflexivity] |]).
split; [unfold ctx_rest_same; repeat split; try assumption; exact S3|]. split.
- intros q Hq. destruct (MEMS q Hq) as (qp & qn & Mq & _). exact (MT_Some_In_keys _ _ _ Mq).
- exact (proj1 (proj1 RING)).
Qed.
Lemma D_MT_ring : forall q, In q (m :: rest) -> nonused (MT A q) /\ nonused (MT A1 q).
Proof.
intros q Hq. destruct DP as (S1 & S2 & S3 & S4 & S5 & S6). cbn [snd] in *.
destruct (MEMS q Hq) as (qp & qn & Mq & _). change (MT A0 q) with (MT A q) in Mq. split; [rewrite Mq; exact I|].
destruct Hq as [<-|Hq]; [rewrite S4; exact I|].
rewrite (S6 q _ Hq Mq). cbn. exact I.
Qed.
Lemma D_MT_other : forall q, ~ In q (QsD rest) -> MT A1 q = MT A q.
Proof.
intros q Hn. destruct DP as (S1 & S2 & S3 & S4 & S5 & S6). cbn [snd] in *.
destruct (in_dec sptr_eq_dec q (m :: rest)) as [Hin|Hout]; [| exact (S5 q Hout)].
destruct Hin as [<-|Hin]; [exfalso; apply Hn; left; reflexivity|].
destruct (MEMS q (or_intror Hin)) as (qp & qn & Mq & _). change (MT A0 q) with (MT A q) in Mq.
rewrite (S6 q _ Hin Mq), Mq. cbn.
destruct (sptr_eqb q (hd m rest)) eqn:E1.
{ exfalso. apply Hn. apply sptr_eqb_eq in E1. unfold QsD. destruct rest; [destruct Hin|]. right. left. symmetry. exact E1. }
destruct (sptr_eqb q (last rest m)) eqn:E2.
{ exfalso. apply Hn. apply sptr_eqb_eq in E2. unfold QsD. destruct rest; [destruct Hin|]. right. right. left. symmetry. exact E2. }
reflexivity.
Qed.
Lemma D_used : used_metas A1 = used_metas A.
Proof.
pose proof D_facts as (_&_&_&EK&_). destruct DP as (S1 & S2 & S3 & S4 & S5 & S6). cbn [snd] in *.
apply (used_metas_same A A1 []); [rewrite EK; exact (proj1 (inv_keys HI)) | rewrite app_nil_r; exact EK |].
intros g am. destruct (in_dec sptr_eq_dec g (m :: rest)) as [Hin|Hout].
- destruct (D_MT_ring g Hin) as [N0 N1]. split; intros H; rewrite H in *; contradiction.
- rewrite (S5 g Hout). tauto.
Qed.
Theorem post_D_core : forall sp mem' md',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD rest sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 L mem' A1 ->
(forall q, In q (QsD rest) ->
cell_mem B L mem' (MCell (LMem (padd q META_prev)) 8 (lnk_prev (MT A1 q))) /\
cell_mem B L mem' (MCell (LMem (padd q META_next)) 8 (lnk_next (MT A1 q)))) ->
(forall x q, In q (QsD rest) -> ptr_addr L q <= x < ptr_addr L q + 16 -> present mem' x) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_halted md' = m_halted md ->
midrep B L A1 mem' md' /\ ama_ok A1 /\ bounded A1 /\ ptr_addr L m <> 0 /\
(forall x q, In q (QsD rest) -> ptr_addr L q <= x < ptr_addr L q + 16 -> in_nonmap_region L A1 x).
Proof.
intros sp mem' md' Hsp FR C11 QC QP EV EL EM EH.
pose proof D_facts as (EAr & ERg & EBk & EK & Ein & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama & Efh & CR & QK & NDr).
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3).
assert (RG : forall k, region_of A1 k = region_of A k) by (intros k; unfold region_of; rewrite ERg; reflexivity).
assert (EA : st_areas A1 = st_areas A ++ []) by (rewrite app_nil_r; exact EAr).
assert (QsK : forall q, In q (QsD rest) -> In q (m :: rest)).
{ intros q Hq. unfold QsD in Hq. destruct Hq as [<-|Hq]; [left; reflexivity|].
destruct rest as [|y r']; [destruct Hq|]. cbn [In] in Hq. destruct Hq as [<-|[<-|[]]].
- right. left. reflexivity.
- right. apply In_last. discriminate. }
assert (QsSlots : forall q, In q (QsD rest) -> exists a k, In a (st_areas A) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of a k).
{ intros q Hq. pose proof (inv_keys HI) as (_ & KP & _). destruct (KP q (QK q (QsK q Hq))) as (a & k & Ha & Hk & ->).
exists a, k. split; [exact Ha|]. split; [| reflexivity]. unfold handed in Hk. destruct (sptr_eqb a _); unfold METAS_PER_AREA in *; pose proof (inv_keys HI) as (_&_&_&_&Kc); lia. }
assert (INPAGE : forall q x, In q (QsD rest) -> ptr_addr L q <= x < ptr_addr L q + 16 ->
exists a, In a (st_areas A) /\ ptr_addr L a <= x < ptr_addr L a + PGSZ).
{ intros q x Hq Hx. destruct (QsSlots q Hq) as (a & k & Ha & Hk & ->). exists a. split; [exact Ha|].
unfold slot_of in Hx. rewrite ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
assert (Wdec : forall x, WD rest sp x \/ ~ WD rest sp x).
{ intros x. unfold WD, am_scratch, ctxW.
assert (DQ : (exists q, In q (QsD rest) /\ ptr_addr L q <= x < ptr_addr L q + 16) \/ ~ (exists q, In q (QsD rest) /\ ptr_addr L q <= x < ptr_addr L q + 16)).
{ clear. induction (QsD rest) as [|q l IH]; [right; intros (q & [] & _)|].
destruct (Z_le_dec (ptr_addr L q) x), (Z_lt_dec x (ptr_addr L q + 16)); try (left; exists q; split; [left; reflexivity | lia]);
(destruct IH as [(q' & H1 & H2)|IH]; [left; exists q'; split; [right; exact H1 | exact H2] | right; intros (q' & [<-|H1] & H2); [lia | apply IH; exists q'; auto]]). }
assert (AD : forall lo hi, (lo <= x < hi) \/ ~ (lo <= x < hi)) by (intros; lia).
destruct DQ as [DQ|DQ]; [left; right; right; exact DQ|].
destruct (AD (sp - AM_STACK) sp); [left; left; left; assumption|].
destruct (AD (errno_addr B) (errno_addr B + 4)); [left; left; right; assumption|].
destruct (AD (ms_ctx B) (ms_ctx B + 12)); [left; right; left; left; assumption|].
destruct (AD (ms_ctx B + 16) (ms_ctx B + 80)); [left; right; left; right; left; assumption|].
destruct (AD (ms_ctx B + 920) (ms_ctx B + 928)); [left; right; left; right; right; assumption|].
right. intros [[Hx|Hx]|[[Hx|[Hx|Hx]]|Hx]]; contradiction. }
assert (NM : forall x q, In q (QsD rest) -> ptr_addr L q <= x < ptr_addr L q + 16 -> in_nonmap_region L A1 x).
{ intros x q Hq Hx. destruct (INPAGE q x Hq Hx) as (a & Ha & Hxa).
apply (area_nonmap A1 L a x Ha Hxa); [| intros k0 rg0 H0 _ _; rewrite RG in H0; exact H0 | intros; reflexivity].
intros k0 rg0 H0 L0 K0. exists rg0. rewrite RG. auto with zarith. }
assert (MEMREP : memrep B L A1 mem').
{ refine (memrep_xfer B X R U L L A A1 mem mem' md HI XC AMA MID D_used [] EA ltac:(intros; discriminate)
_ ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto)
eq_refl eq_refl ltac:(intros; reflexivity) (WD rest sp) Wdec FR _ (QsD rest) _ _ QsSlots _ _ _ _ _ _).
- rewrite EAr. exact (proj1 (inv_areas HI)).
- intros x k rg HWx Hk Hl Hkd. destruct HWx as [Hs|[Hc|(q & Hq & Hx)]].
+ exact (scratch_not_region sp x k rg Hsp Hs Hk Hl).
+ exact (ctxW_not_region x k rg Hc Hk Hl).
+ destruct (NM x q Hq Hx) as [_ K]. intros Hxr. apply K. exists k, rg. rewrite RG. auto.
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|(q & Hq & Hxq)]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ left. exists q. auto.
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|(q & Hq & Hxq)]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ exact (QP x q Hq Hxq).
- intros q Hq. destruct (D_MT_ring q (QsK q Hq)) as [N0 N1]. split; [exact N0|]. split; [exact N1|]. exact (QC q Hq).
- intros a k Ha Hk Hnin. apply D_MT_other. exact Hnin.
- intros p Hp. discriminate.
- intros p c Hp. discriminate.
- intros p x Hp. discriminate.
- apply (CTX_std L mem' A1 (WD rest sp) (mid_ctx _ _ _ _ _ MID) C11 CR).
intros x HWx Hcx. destruct HWx as [Hs|[Hc|(q & Hq & Hxq)]]; [| exact Hc |].
* exfalso. destruct Hs as [Hs|Hs]; [pose proof (so_ctx_hi _ SO); unfold AM_STACK in *; lia | exact (ENC x Hs Hcx)].
* exfalso. destruct (INPAGE q x Hq Hxq) as (a & Ha & Hxa). destruct (areas_off_img _ x Ha Hxa) as [Hi _]. apply Hi. apply (so_ctx_img _ SO). exact Hcx. }
split; [|split; [|split; [|split]]].
- split.
+ exact SO.
+ exact MEMREP.
+ apply (tail_geom_xfer B X R U L L A A1 mem md HI XC MID D_used); [intros k rg Hk; rewrite RG; auto | reflexivity | intros; reflexivity].
+ apply (statics_xfer B mem mem' (WD rest sp) SO (mid_statics _ _ _ _ _ MID) FR).
intros x Hst [Hs|[Hc|(q & Hq & Hxq)]].
* destruct Hs as [Hs|Hs]; [| exact (ENS x Hs Hst)].
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hst)). unfold AM_STACK in *. lia.
* apply (SNC x Hst). unfold ctxW, CTX_SIZE in *. lia.
* destruct (INPAGE q x Hq Hxq) as (a & Ha & Hxa). destruct (areas_off_img _ x Ha Hxa) as [Hi _]. exact (Hi (so_statics_img _ SO x Hst)).
+ destruct (ledger_same B L A md LG LX A1 md' ERg EBk EV EL EM) as [G _]. exact G.
+ destruct (ledger_same B L A md LG LX A1 md' ERg EBk EV EL EM) as [_ G]. exact G.
+ refine (layout_ok_xfer B X R U L L A A1 mem md HI MID [] EA ltac:(intros; discriminate)
ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto) eq_refl ltac:(intros; reflexivity) _ _ _ _ _).
* rewrite ERg. lia.
* intros; discriminate.
* intros; discriminate.
* intros k rg Hk H'. rewrite RG in H'. pose proof (region_of_lt _ _ _ H'). exfalso. unfold N in *. lia.
* intros k rg' Hk H' Hl. rewrite RG in H'. exists rg'. auto.
+ exact (mid_ctx _ _ _ _ _ MID).
+ exact (mid_sec _ _ _ _ _ MID).
+ rewrite EH, EL, EM. exact (conj M1 (conj M2 M3)).
- unfold ama_ok in *. rewrite EAr, Eama, ERg. exact AMA.
- apply bounded_keep; [destruct CR as (_&_&_&EU&_); exact EU | rewrite Esh; lia | destruct BND as (_ & B2 & _); rewrite Esh; lia | rewrite EAr; lia].
- destruct (INPAGE m (ptr_addr L m) ltac:(left; reflexivity) ltac:(lia)) as (a & Ha & Hxa). destruct (areas_off_img _ _ Ha Hxa) as [_ Hr]. lia.
- exact NM.
Qed.
End b0.
End a0.
Definition pagebyte (sec : Z) (i : Z) : Z :=
if i <? 8 then le_byte sec 8 (Z.to_nat i)
else if (16 <=? i) && (i <? 20) then le_byte METAS_PER_AREA 4 (Z.to_nat (i - 16)) else 0.
Section c0.
Variables (s3 : astate) (p : sptr) (L' : layout) (md3 : Model).
Let A' := take_st (open_st p s3).
Let m := padd p AREA_HDR.
Hypothesis S3areas : st_areas s3 = st_areas A.
Hypothesis S3metas : st_metas s3 = st_metas A.
Hypothesis S3ama : st_avail_meta_areas s3 = p.
Hypothesis S3init : st_init_done s3 = true.
Hypothesis S3rest : ctx_rest_same s3.
Hypothesis S3hd : st_area_head s3 = st_area_head A.
Hypothesis S3tl : st_area_tail s3 = st_area_tail A.
Hypothesis S3fh : st_free_meta_head s3 = st_free_meta_head A.
Hypothesis S3sh : 0 <= st_meta_alloc_shift s3 <= 40.
Hypothesis RGmap : forall k rg, region_of s3 k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of A k = Some rg.
Hypothesis RGkeep : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of s3 k = Some rg.
Hypothesis RGnonmap : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
exists rg', region_of s3 k = Some rg' /\ rg_live rg' = true /\ rg_kind rg' <> RkMap /\ rg_len rg <= rg_len rg'.
Hypothesis LIVEold : forall k rg', (k < N)%nat -> region_of s3 k = Some rg' -> rg_live rg' = true -> exists rg, region_of A k = Some rg /\ rg_live rg = true.
Hypothesis LEN3 : (N <= length (st_regions s3))%nat.
Hypothesis NN3 : forall k rg, region_of s3 k = Some rg -> 0 <= rg_len rg.
Hypothesis L'ctx : ly_ctx L' = ly_ctx L.
Hypothesis L'sec : ly_sec L' = ly_sec L.
Hypothesis L'reg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r.
Hypothesis L'aln : forall k rg, (N <= k)%nat -> region_of s3 k = Some rg -> rg_live rg = true -> ly_reg L' k mod PGSZ = 0.
Hypothesis LG3 : ledger_ok B L' s3 md3.
Hypothesis LX3 : ledger_x L' s3 md3.
Hypothesis MD3 : m_halted md3 = None /\ m_vm_lazy md3 = [] /\ m_vm_materialized md3 = [].
Hypothesis HI' : Inv (m :: X) R U A'.
Hypothesis Ppage : exists rg, region_of s3 (prid p) = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
PGSZ <= poff p /\ poff p + PGSZ <= rg_len rg /\ poff p mod PGSZ = 0.
Hypothesis Pfresh : forall e, In e (footprint A) -> ranges_disjoint (ptr_addr L' p, PGSZ) (crange L e).
Hypothesis Pnomap : forall k rg x, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg).
Variable Kr : Z -> Prop.
Hypothesis Krdec : forall x, Kr x \/ ~ Kr x.
Hypothesis Kr_area : forall x a, Kr x -> In a (st_areas A) -> ~ (ptr_addr L a <= x < ptr_addr L a + PGSZ).
Hypothesis Kr_map : forall x k rg, Kr x -> region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> ~ (ly_reg L k <= x < ly_reg L k + rg_len rg).
Hypothesis Kr_img : forall x, Kr x -> ~ in_img B x.
Hypothesis Kr_ctx : forall x, Kr x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Definition WO (sp : Z) (x : Z) : Prop :=
am_scratch sp x \/ ctxW x \/
(st_areas A <> [] /\ ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16) \/
(ptr_addr L' p <= x < ptr_addr L' p + PGSZ) \/ Kr x.
Lemma A'_unfold : A' = upd_meta m MRaw (set_avail_meta (padd m META_SIZE) (set_avail_meta_count (METAS_PER_AREA - 1) (open_st p s3))).
Proof. reflexivity. Qed.
Lemma p_addr : forall k, 0 <= k -> ptr_addr L' (slot_of p k) = ptr_addr L' p + AREA_HDR + META_SIZE * k.
Proof. intros k Hk. unfold slot_of. rewrite ptr_addr_padd. lia. Qed.
Lemma m_fresh : forall k, 0 <= k < METAS_PER_AREA -> ~ In (slot_of p k) (keys A).
Proof.
intros k Hk Hin. pose proof (inv_keys HI) as (_ & KP & _). destruct (KP _ Hin) as (a & j & Ha & Hj & Eq).
pose proof (Pfresh (LMem a, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists a; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem a)) with (ptr_addr L a) in D.
pose proof (f_equal (ptr_addr L') Eq) as E1. rewrite p_addr in E1 by lia. rewrite ptr_addr_padd in E1.
rewrite (area_addr_old X R U L L' A HI L'ctx L'reg a Ha) in E1.
unfold handed in Hj. destruct (sptr_eqb a _); unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; pose proof (inv_keys HI) as (_&_&_&_&Kc); lia.
Qed.
Lemma O_fields :
st_areas A' = st_areas A ++ [p] /\ st_regions A' = st_regions s3 /\ st_brk A' = st_brk s3 /\
st_init_done A' = true /\ st_avail_meta A' = padd m META_SIZE /\ st_avail_meta_count A' = METAS_PER_AREA - 1 /\
st_avail_meta_area_count A' = st_avail_meta_area_count s3 - 1 /\ st_meta_alloc_shift A' = st_meta_alloc_shift s3 /\
st_area_head A' = (match st_area_head A with None => Some p | h => h end) /\ st_area_tail A' = Some p /\
st_avail_meta_areas A' = padd p 4096 /\ st_free_meta_head A' = st_free_meta_head A /\ ctx_rest_same A' /\
keys A' = keys A ++ [m] /\ (forall q, MT A' q = if sptr_eqb q m then Some MRaw else MT A q).
Proof.
destruct S3rest as (R1&R2&R3&R4&R5&R6).
assert (K : keys A' = keys A ++ [m]).
{ rewrite A'_unfold. rewrite keys_upd_notIn; [unfold keys; cbn; rewrite S3metas; reflexivity|].
unfold keys. cbn. rewrite S3metas. exact (m_fresh 0 ltac:(unfold METAS_PER_AREA; lia)). }
assert (M' : forall q, MT A' q = if sptr_eqb q m then Some MRaw else MT A q).
{ intros q. rewrite A'_unfold. destruct (sptr_eqb q m) eqn:E.
+ apply sptr_eqb_eq in E. subst q. apply MT_upd_same.
+ rewrite MT_upd_other; [unfold MT; cbn; rewrite S3metas; reflexivity|]. intros ->. rewrite sptr_eqb_refl in E. discriminate. }
unfold ctx_rest_same. rewrite A'_unfold. cbn -[Z.sub METAS_PER_AREA padd]. rewrite S3areas, S3hd.
repeat split; try reflexivity; try assumption.
Qed.
Lemma p_range : 4096 <= ptr_addr L' p /\ ptr_addr L' p + PGSZ <= alloc_ceiling /\
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> ~ in_img B x) /\ ptr_addr L' p mod PGSZ = 0.
Proof.
destruct Ppage as (rg & Hr & Hl & Hk & Ho1 & Ho2 & Ho3). destruct p as [r o]. cbn [prid poff] in *.
pose proof (lg_placed _ _ _ _ LG3 r rg Hr Hl) as (Pal & Plo & Phi & Pimg). unfold ptr_addr. cbn.
split; [unfold PGSZ in *; lia|]. split; [lia|]. split; [intros x Hx; apply Pimg; lia|].
unfold PGSZ in *. rewrite Z.add_mod, Pal, Ho3 by lia. reflexivity.
Qed.
Lemma padd_padd' : forall q a b, padd (padd q a) b = padd q (a + b).
Proof. intros [r o] a b. cbn. f_equal. lia. Qed.
Lemma NEW_cells_ok : forall mem',
(forall i, 0 <= i < PGSZ -> mbyte (ms_segs B) mem' (ptr_addr L' p + i) = Some (Z_to_bv 8 (pagebyte (ly_sec L) i))) ->
forall c, In c (area_cells A' p None) -> cell_mem B L' mem' c.
Proof.
intros mem' PG c Hc. pose proof O_fields as (_&_&_&_&_&_&_&_&_&_&_&_&_& K & M').
assert (ZC : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= PGSZ -> ((8 <= d /\ d + Z.of_nat w <= 16) \/ 20 <= d) ->
cell_mem B L' mem' (MCell (LMem (padd p d)) w (VZ 0))).
{ intros d w Hd1 Hd2 Hd3. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros j Hj.
change (loc_addr L' (LMem (padd p d))) with (ptr_addr L' (padd p d)). rewrite ptr_addr_padd.
replace (ptr_addr L' p + d + Z.of_nat j) with (ptr_addr L' p + (d + Z.of_nat j)) by lia.
rewrite PG by lia. rewrite YN03.le_byte_0. unfold pagebyte.
replace (d + Z.of_nat j <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace ((16 <=? d + Z.of_nat j) && (d + Z.of_nat j <? 20)) with false; [reflexivity|].
symmetry. apply andb_false_iff. destruct Hd3; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
apply In_area_cells_split in Hc as [Hh | (k & Hk & Hsl)].
- cbn [hdr_cells In] in Hh. destruct Hh as [<-|[<-|[<-|[]]]].
+   unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite L'sec.
intros j Hj. change (loc_addr L' (LMem p)) with (ptr_addr L' p). rewrite PG by (unfold PGSZ; lia).
unfold pagebyte. replace (Z.of_nat j <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id. reflexivity.
+ cbn [optr]. apply ZC; unfold PGSZ; lia.
+ unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros j Hj.
change (loc_addr L' (LMem (padd p 16))) with (ptr_addr L' (padd p 16)). rewrite ptr_addr_padd.
replace (ptr_addr L' p + 16 + Z.of_nat j) with (ptr_addr L' p + (16 + Z.of_nat j)) by lia. rewrite PG by (unfold PGSZ; lia).
unfold pagebyte. replace (16 + Z.of_nat j <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace ((16 <=? 16 + Z.of_nat j) && (16 + Z.of_nat j <? 20)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace (Z.to_nat (16 + Z.of_nat j - 16)) with j by lia. reflexivity.
- rewrite M' in Hsl.
assert (EQ : sptr_eqb (slot_of p k) m = (k =? 0)).
{ unfold m, slot_of. destruct (Z.eqb_spec k 0) as [->|Hne].
- replace (AREA_HDR + META_SIZE * 0) with AREA_HDR by lia. apply sptr_eqb_refl.
- destruct (sptr_eqb (padd p (AREA_HDR + META_SIZE * k)) (padd p AREA_HDR)) eqn:E; [|reflexivity].
apply sptr_eqb_eq in E. pose proof (f_equal poff E) as E2. destruct p. cbn in E2. unfold META_SIZE in E2. lia. }
rewrite EQ in Hsl.
assert (NONE : (k =? 0) = false -> MT A (slot_of p k) = None).
{ intros Hk0. apply mlookup_None_iff. apply m_fresh. exact Hk. }
assert (CELLS : In c [MCell (LMem (padd (slot_of p k) META_prev)) 8 (VZ 0); MCell (LMem (padd (slot_of p k) META_next)) 8 (VZ 0);
MCell (LMem (padd (slot_of p k) META_mem)) 8 (VZ 0); MCell (LMem (padd (slot_of p k) META_avail)) 4 (VZ 0);
MCell (LMem (padd (slot_of p k) META_freed)) 4 (VZ 0); MCell (LMem (padd (slot_of p k) META_bits)) 8 (VZ 0)]).
{ destruct (k =? 0); [exact Hsl|]. rewrite (NONE eq_refl) in Hsl. exact Hsl. }
unfold slot_of in CELLS. rewrite !padd_padd' in CELLS.
cbn [In] in CELLS. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, AREA_HDR, META_SIZE in CELLS.
unfold METAS_PER_AREA in Hk.
destruct CELLS as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; apply ZC; unfold PGSZ; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
Lemma O_used : used_metas A' = used_metas A.
Proof.
pose proof O_fields as (_&_&_&_&_&_&_&_&_&_&_&_&_& K & M').
apply (used_metas_same A A' [m]); [exact (proj1 (inv_keys HI')) | exact K |].
intros g am. rewrite M'. destruct (sptr_eqb g m) eqn:E; [|tauto].
apply sptr_eqb_eq in E. subst g. split; [discriminate|]. intros H. exfalso.
apply (m_fresh 0 ltac:(unfold METAS_PER_AREA; lia)). unfold slot_of. replace (AREA_HDR + META_SIZE * 0) with AREA_HDR by lia. exact (MT_Some_In_keys _ _ _ H).
Qed.
Theorem post_open : forall sp mem',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WO sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 L' mem' A' ->
(st_areas A <> [] -> forall k, (k < 8)%nat ->
mbyte (ms_segs B) mem' (ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ptr_addr L' p) 8 k))) ->
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> present mem' x) ->
(forall i, 0 <= i < PGSZ -> mbyte (ms_segs B) mem' (ptr_addr L' p + i) = Some (Z_to_bv 8 (pagebyte (ly_sec L) i))) ->
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> present mem' x) ->
midrep B L' A' mem' md3 /\ ama_ok A' /\ bounded A' /\ ptr_addr L' m <> 0 /\
(forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> in_nonmap_region L' A' x) /\
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> in_nonmap_region L' A' x).
Proof.
intros sp mem' Hsp FR C11 NXT NXTP PG PGP.
pose proof O_fields as (EAr & ERg & EBk & Ein & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama & Efh & CR & K & M').
pose proof p_range as (P1 & P2 & P3 & P4). pose proof (proj1 alloc_ceiling_val) as AC.
assert (RG : forall k, region_of A' k = region_of s3 k) by (intros k; unfold region_of; rewrite ERg; reflexivity).
assert (Hlast : st_areas A <> [] -> In (last (st_areas A) (SP 0%nat 0)) (st_areas A)) by (intros Hne; apply In_last; exact Hne).
assert (Wdec : forall x, WO sp x \/ ~ WO sp x).
{ intros x. pose proof (Krdec x) as D5.
assert (D1 : am_scratch sp x \/ ~ am_scratch sp x) by (unfold am_scratch; lia).
assert (D2 : ctxW x \/ ~ ctxW x) by (unfold ctxW; lia).
assert (D4 : (ptr_addr L' p <= x < ptr_addr L' p + PGSZ) \/ ~ (ptr_addr L' p <= x < ptr_addr L' p + PGSZ)) by lia.
assert (D3 : (st_areas A <> [] /\ ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16) \/
~ (st_areas A <> [] /\ ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16)).
{ destruct (nil_or_not (st_areas A)) as [EA0|EA0]; [right; intros [Hne _]; exact (Hne EA0)|].
destruct (Z_le_dec (ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8) x); [|right; intros [_ Hr]; lia].
destruct (Z_lt_dec x (ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16)); [left; split; [exact EA0 | lia] | right; intros [_ Hr]; lia]. }
unfold WO. destruct D1 as [K1|K1]; [left; left; exact K1|]. destruct D2 as [K2|K2]; [left; right; left; exact K2|].
destruct D3 as [K3|K3]; [left; right; right; left; exact K3|]. destruct D4 as [K4|K4]; [left; right; right; right; left; exact K4|].
destruct D5 as [K5|K5]; [left; right; right; right; right; exact K5|].
right. intros [Z1|[Z2|[Z3|[Z4|Z5]]]]; contradiction. }
assert (NMp : forall x, ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> in_nonmap_region L' A' x).
{ intros x Hx. destruct Ppage as (rg & Hr & Hl & Hk & Ho1 & Ho2 & Ho3). split.
- exists (prid p), rg. rewrite RG. destruct p as [r o]. cbn [prid poff] in *. unfold ptr_addr in Hx. cbn in Hx. repeat split; try assumption; lia.
- intros (k & rg2 & Hk2 & Hl2 & Hkd2 & Hx2). rewrite RG in Hk2. pose proof (RGmap k rg2 Hk2 Hl2 Hkd2) as HkA.
rewrite (L'reg k (region_of_lt _ _ _ HkA)) in Hx2. exact (Pnomap k rg2 x HkA Hl2 Hkd2 Hx Hx2). }
assert (NMn : st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> in_nonmap_region L' A' x).
{ intros Hne x Hx. apply (area_nonmap A' L' (last (st_areas A) (SP 0%nat 0)) x (Hlast Hne)); [unfold PGSZ; lia | | |].
- intros k rg Hk Hl Hkd. destruct (RGnonmap k rg Hk Hl Hkd) as (rg' & H1 & H2 & H3 & H4). exists rg'. rewrite RG. auto.
- intros k rg Hk Hl Hkd. rewrite RG in Hk. exact (RGmap k rg Hk Hl Hkd).
- exact L'reg. }
assert (MEMREP : memrep B L' A' mem').
{ refine (memrep_xfer B X R U L L' A A' mem mem' md HI XC AMA MID O_used [p] EAr ltac:(intros; discriminate)
(proj1 (inv_areas HI')) ltac:(intros k rg Hk; rewrite RG in Hk; apply RGmap; exact Hk) ltac:(intros k rg Hk Hl Hkd; rewrite RG; exact (RGkeep k rg Hk Hl Hkd))
L'ctx L'sec L'reg (WO sp) Wdec FR _ [] _ _ _ _ _ _ _ _ _).
- intros x k rg HWx Hk Hl Hkd. destruct HWx as [Hs|[Hc|[[Hne Hn]|[Hp|Hk']]]].
+ exact (scratch_not_region sp x k rg Hsp Hs Hk Hl).
+ exact (ctxW_not_region x k rg Hc Hk Hl).
+ destruct (NMn Hne x Hn) as [_ NM]. intros Hx. apply NM. exists k, rg. rewrite RG. rewrite (L'reg k (region_of_lt _ _ _ Hk)). auto using RGkeep.
+ exact (Pnomap k rg x Hk Hl Hkd Hp).
+ exact (Kr_map x k rg Hk' Hk Hl Hkd).
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|[[Hne Hn]|[Hp|Hk']]]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ right. split; [discriminate | exact Hn].
+ exfalso. pose proof (Pfresh (LMem a, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists a; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem a)) with (ptr_addr L a) in D. lia.
+ exfalso. exact (Kr_area x a Hk' Ha Hx).
- intros x a HWx Ha Hx. destruct HWx as [Hs|[Hc|[[Hne Hn]|[Hp|Hk']]]].
+ exfalso. exact (scratch_not_area sp x a Hsp Hs Ha Hx).
+ exfalso. exact (ctxW_not_area x a Hc Ha Hx).
+ exact (NXTP Hne x Hn).
+ exfalso. pose proof (Pfresh (LMem a, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists a; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem a)) with (ptr_addr L a) in D. lia.
+ exfalso. exact (Kr_area x a Hk' Ha Hx).
- intros q [].
- intros q [].
- intros a k Ha Hk _. rewrite M'. destruct (sptr_eqb (slot_of a k) m) eqn:E; [|reflexivity].
exfalso. apply sptr_eqb_eq in E. pose proof (inv_keys HI) as (_ & KP & _).
apply (m_fresh 0 ltac:(unfold METAS_PER_AREA; lia)). unfold slot_of at 1. replace (AREA_HDR + META_SIZE * 0) with AREA_HDR by lia. fold m. rewrite <- E.
exfalso. pose proof (Pfresh (LMem a, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists a; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem a)) with (ptr_addr L a) in D.
pose proof (f_equal (ptr_addr L') E) as E1. unfold slot_of in E1. unfold m in E1. rewrite !ptr_addr_padd in E1.
rewrite (area_addr_old X R U L L' A HI L'ctx L'reg a Ha) in E1. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
- intros p' Hp' Hne. injection Hp' as <-. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num].
intros j Hj. change (loc_addr L' (LMem ?q)) with (ptr_addr L' q). rewrite ptr_addr_padd.
rewrite (area_addr_old X R U L L' A HI L'ctx L'reg _ (Hlast Hne)). change (loc_addr L' (LMem p)) with (ptr_addr L' p). exact (NXT Hne j Hj).
- intros p' c Hp'. injection Hp' as <-. apply NEW_cells_ok. exact PG.
- intros p' x Hp'. injection Hp' as <-. exact (PGP x).
- apply (CTX_std L' mem' A' (WO sp) ltac:(rewrite L'ctx; exact (mid_ctx _ _ _ _ _ MID)) C11 CR).
intros x HWx Hcx. destruct HWx as [Hs|[Hc|[[Hne Hn]|[Hp|Hk']]]]; [| exact Hc | | |].
* exfalso. destruct Hs as [Hs|Hs]; [pose proof (so_ctx_hi _ SO); unfold AM_STACK in *; lia | exact (ENC x Hs Hcx)].
* exfalso. destruct (areas_off_img _ x (Hlast Hne) ltac:(unfold PGSZ; lia)) as [Hi _]. apply Hi. apply (so_ctx_img _ SO). exact Hcx.
* exfalso. apply (P3 x Hp). apply (so_ctx_img _ SO). exact Hcx.
* exfalso. exact (Kr_ctx x Hk' Hcx). }
split; [|split; [|split; [|split; [|split]]]].
- split.
+ exact SO.
+ exact MEMREP.
+ apply (tail_geom_xfer B X R U L L' A A' mem md HI XC MID O_used); [intros k rg Hk Hl Hkd; rewrite RG; exact (RGkeep k rg Hk Hl Hkd) | exact L'ctx | exact L'reg].
+ apply (statics_xfer B mem mem' (WO sp) SO (mid_statics _ _ _ _ _ MID) FR).
intros x Hst [Hs|[Hc|[[Hne Hn]|[Hp|Hk']]]].
* destruct Hs as [Hs|Hs]; [| exact (ENS x Hs Hst)]. pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hst)). unfold AM_STACK in *. lia.
* apply (SNC x Hst). unfold ctxW, CTX_SIZE in *. lia.
* destruct (areas_off_img _ x (Hlast Hne) ltac:(unfold PGSZ; lia)) as [Hi _]. exact (Hi (so_statics_img _ SO x Hst)).
* exact (P3 x Hp (so_statics_img _ SO x Hst)).
* exact (Kr_img x Hk' (so_statics_img _ SO x Hst)).
+ destruct (ledger_same B L' s3 md3 LG3 LX3 A' md3 ERg EBk eq_refl eq_refl eq_refl) as [G _]. exact G.
+ destruct (ledger_same B L' s3 md3 LG3 LX3 A' md3 ERg EBk eq_refl eq_refl eq_refl) as [_ G]. exact G.
+ refine (layout_ok_xfer B X R U L L' A A' mem md HI MID [p] EAr ltac:(intros; discriminate)
ltac:(intros k rg Hk; rewrite RG in Hk; apply RGmap; exact Hk) ltac:(intros k rg Hk Hl Hkd; rewrite RG; exact (RGkeep k rg Hk Hl Hkd)) L'ctx L'reg _ _ _ _ _).
* rewrite ERg. exact LEN3.
* intros p' e Hp' He. injection Hp' as <-. exact (Pfresh e He).
* intros p' Hp'. injection Hp' as <-. lia.
* intros k rg Hk H'. rewrite RG in H'. exact (L'aln k rg Hk H').
* intros k rg' Hk H'. rewrite RG in H'. exact (LIVEold k rg' Hk H').
+ rewrite L'ctx. exact (mid_ctx _ _ _ _ _ MID).
+ rewrite L'sec. exact (mid_sec _ _ _ _ _ MID).
+ exact MD3.
- unfold ama_ok. rewrite Eama, ERg. intros _. destruct Ppage as (rg & Hr & _). destruct p as [r o]. cbn [prid padd]. exact (region_of_lt _ _ _ Hr).
- destruct BND as (B1 & B2 & B3). pose proof areas_count_bound. unfold bounded, usage_of in *.
destruct CR as (_&_&_&EU&_). rewrite EU, Esh, EAr, length_app. cbn [length]. repeat split; try apply B1; try lia.
- unfold m. rewrite ptr_addr_padd. unfold AREA_HDR. lia.
- exact NMp.
- exact NMn.
Qed.
End c0.
Section d0.
Variable A' : astate.
Hypothesis F_regions : st_regions A' = st_regions A.
Hypothesis F_areas : st_areas A' = st_areas A.
Hypothesis F_metas : st_metas A' = st_metas A.
Hypothesis F_brk : st_brk A' = st_brk A \/ st_brk A' = BrkDead.
Hypothesis F_init : st_init_done A' = true.
Hypothesis F_rest : ctx_rest_same A'.
Hypothesis F_fh : st_free_meta_head A' = st_free_meta_head A.
Hypothesis F_am : st_avail_meta A' = st_avail_meta A.
Hypothesis F_amc : st_avail_meta_count A' = st_avail_meta_count A.
Hypothesis F_aac : st_avail_meta_area_count A' = st_avail_meta_area_count A.
Hypothesis F_sh : st_meta_alloc_shift A' = st_meta_alloc_shift A.
Hypothesis F_hd : st_area_head A' = st_area_head A.
Hypothesis F_tl : st_area_tail A' = st_area_tail A.
Hypothesis F_ama : st_avail_meta_areas A' = st_avail_meta_areas A.
Definition WF0 (sp : Z) (x : Z) : Prop := am_scratch sp x \/ ctxW x.
Theorem post_fail0 : forall sp mem' md',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WF0 sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 L mem' A' ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md -> m_halted md' = m_halted md ->
midrep B L A' mem' md' /\ ama_ok A' /\ bounded A'.
Proof.
intros sp mem' md' Hsp FR C11 EV EL EM EH.
pose proof (mid_md _ _ _ _ _ MID) as (M1 & M2 & M3).
assert (RG : forall k, region_of A' k = region_of A k) by (intros k; unfold region_of; rewrite F_regions; reflexivity).
assert (EA : st_areas A' = st_areas A ++ []) by (rewrite app_nil_r; exact F_areas).
assert (EK : keys A' = keys A) by (unfold keys; rewrite F_metas; reflexivity).
assert (UM : used_metas A' = used_metas A) by (unfold used_metas; rewrite F_metas; reflexivity).
assert (Wdec : forall x, WF0 sp x \/ ~ WF0 sp x) by (intros x; unfold WF0, am_scratch, ctxW; lia).
assert (MEMREP : memrep B L A' mem').
{ refine (memrep_xfer B X R U L L A A' mem mem' md HI XC AMA MID UM [] EA ltac:(intros; discriminate)
_ ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto)
eq_refl eq_refl ltac:(intros; reflexivity) (WF0 sp) Wdec FR _ [] _ _ _ _ _ _ _ _ _).
- rewrite F_areas. exact (proj1 (inv_areas HI)).
- intros x k rg [Hs|Hc] Hk Hl Hkd; [exact (scratch_not_region sp x k rg Hsp Hs Hk Hl) | exact (ctxW_not_region x k rg Hc Hk Hl)].
- intros x a [Hs|Hc] Ha Hx; exfalso; [exact (scratch_not_area sp x a Hsp Hs Ha Hx) | exact (ctxW_not_area x a Hc Ha Hx)].
- intros x a [Hs|Hc] Ha Hx; exfalso; [exact (scratch_not_area sp x a Hsp Hs Ha Hx) | exact (ctxW_not_area x a Hc Ha Hx)].
- intros q [].
- intros q [].
- intros a k _ _ _. unfold MT. rewrite F_metas. reflexivity.
- intros; discriminate.
- intros; discriminate.
- intros; discriminate.
- apply (CTX_std L mem' A' (WF0 sp) (mid_ctx _ _ _ _ _ MID) C11 F_rest).
intros x [Hs|Hc] Hcx; [| exact Hc].
exfalso. destruct Hs as [Hs|Hs]; [pose proof (so_ctx_hi _ SO); unfold AM_STACK in *; lia | exact (ENC x Hs Hcx)]. }
assert (LGX : ledger_ok B L A' md' /\ ledger_x L A' md').
{ destruct F_brk as [EB|EB].
- exact (ledger_same B L A md LG LX A' md' F_regions EB EV EL EM).
- exact (ledger_brk_dead B L A md LG LX A' md' F_regions EB EV EL EM). }
split; [|split].
- split.
+ exact SO.
+ exact MEMREP.
+ apply (tail_geom_xfer B X R U L L A A' mem md HI XC MID UM); [intros k rg Hk; rewrite RG; auto | reflexivity | intros; reflexivity].
+ apply (statics_xfer B mem mem' (WF0 sp) SO (mid_statics _ _ _ _ _ MID) FR).
intros x Hst [Hs|Hc].
* destruct Hs as [Hs|Hs]; [| exact (ENS x Hs Hst)]. pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hst)). unfold AM_STACK in *. lia.
* apply (SNC x Hst). unfold ctxW, CTX_SIZE in *. lia.
+ exact (proj1 LGX).
+ exact (proj2 LGX).
+ refine (layout_ok_xfer B X R U L L A A' mem md HI MID [] EA ltac:(intros; discriminate)
ltac:(intros k rg Hk; rewrite RG in Hk; auto) ltac:(intros k rg Hk; rewrite RG; auto) eq_refl ltac:(intros; reflexivity) _ _ _ _ _).
* rewrite F_regions. lia.
* intros; discriminate.
* intros; discriminate.
* intros k rg Hk H'. rewrite RG in H'. pose proof (region_of_lt _ _ _ H'). exfalso. unfold N in *. lia.
* intros k rg' Hk H' Hl. rewrite RG in H'. exists rg'. auto.
+ exact (mid_ctx _ _ _ _ _ MID).
+ exact (mid_sec _ _ _ _ _ MID).
+ rewrite EH, EL, EM. exact (conj M1 (conj M2 M3)).
- unfold ama_ok in *. rewrite F_areas, F_ama, F_regions. exact AMA.
- apply bounded_keep; [destruct F_rest as (_&_&_&EU&_); exact EU | rewrite F_sh; lia | destruct BND as (_ & B2 & _); rewrite F_sh; lia | rewrite F_areas; lia].
Qed.
End d0.
Definition like_A0 (Xs : astate) : Prop :=
st_regions Xs = st_regions A /\ st_areas Xs = st_areas A /\ st_metas Xs = st_metas A /\
(st_brk Xs = st_brk A \/ st_brk Xs = BrkDead) /\ st_init_done Xs = true /\ ctx_rest_same Xs /\
st_free_meta_head Xs = st_free_meta_head A /\ st_avail_meta Xs = st_avail_meta A /\
st_avail_meta_count Xs = st_avail_meta_count A /\ st_avail_meta_area_count Xs = st_avail_meta_area_count A /\
st_meta_alloc_shift Xs = st_meta_alloc_shift A /\ st_area_head Xs = st_area_head A /\ st_area_tail Xs = st_area_tail A /\
st_avail_meta_areas Xs = st_avail_meta_areas A.
Lemma like_A0_A0 : like_A0 A0.
Proof. unfold like_A0, ctx_rest_same, A0. cbn. repeat split; try reflexivity. left. reflexivity. Qed.
Lemma like_A0_dead : like_A0 (set_brk BrkDead A0).
Proof. unfold like_A0, ctx_rest_same, A0. cbn. repeat split; try reflexivity. right. reflexivity. Qed.
Lemma ledger_like : forall Xs, like_A0 Xs -> ledger_ok B L Xs md /\ ledger_x L Xs md.
Proof.
intros Xs (ER & _ & _ & EB & _). destruct EB as [EB|EB].
- exact (ledger_same B L A md LG LX Xs md ER EB eq_refl eq_refl eq_refl).
- exact (ledger_brk_dead B L A md LG LX Xs md ER EB eq_refl eq_refl eq_refl).
Qed.
Section e0.
Variables (Xs : astate) (a : word) (md' : Model).
Hypothesis LXs : like_A0 Xs.
Hypothesis Haac : st_avail_meta_area_count A = 0.
Let len := Z.shiftl 2 (st_meta_alloc_shift A) * PGSZ.
Let A' := resv_st Xs.
Let L' := Lset L A (bv_unsigned a).
Hypothesis PL : place_ok (Z_to_bv 64 0) md a len = true.
Hypothesis MD' : m_vmmaps md' = m_vmmaps (mmap_none_model a (Z_to_bv 64 len) md) /\ m_halted md' = None /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = [].
Definition WRF (sp : Z) (x : Z) : Prop := am_scratch sp x \/ ctxW x \/ (bv_unsigned a <= x < bv_unsigned a + len).
Lemma len_facts : 0 < len /\ len mod PGSZ = 0 /\ bv_unsigned a + len <= alloc_ceiling /\ 0 < bv_unsigned a /\
bv_unsigned a mod PGSZ = 0 /\
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 len) = true /\
st_meta_alloc_shift A + 1 <= 40.
Proof.
destruct BND as (_ & B2 & _). pose proof (proj1 alloc_ceiling_val) as AC.
assert (Hlen : len = 2 ^ (st_meta_alloc_shift A + 1) * 4096).
{ unfold len. rewrite Z.shiftl_mul_pow2 by lia. change PGSZ with 4096. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. }
assert (Hpos : 0 < 2 ^ (st_meta_alloc_shift A + 1)) by (apply Z.pow_pos_nonneg; lia).
unfold place_ok in PL. apply andb_prop in PL as [PL RF]. apply andb_prop in PL as [PL Htop].
apply andb_prop in PL as [Hal Ha0]. apply Z.eqb_eq in Hal. apply Z.ltb_lt in Ha0. apply Z.leb_le in Htop. unfold page_size in Hal.
assert (Hlmod : len mod PGSZ = 0) by (rewrite Hlen; change PGSZ with 4096; apply Z_mod_mult).
assert (Hceil : bv_unsigned a + len <= alloc_ceiling).
{ apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ LG)); [| exact Htop].
rewrite Z.add_mod, Hal by lia. unfold PGSZ in Hlmod. rewrite Hlmod. reflexivity. }
split; [lia|]. split; [exact Hlmod|]. split; [exact Hceil|]. split; [exact Ha0|].
split; [exact Hal|]. split; [exact RF|].
destruct (Z_lt_le_dec (st_meta_alloc_shift A + 1) 35) as [Hs|Hs]; [lia|]. exfalso.
assert (2 ^ 35 <= 2 ^ (st_meta_alloc_shift A + 1)) by (apply Z.pow_le_mono_r; lia).
change (2 ^ 35) with 34359738368 in H. clear -Hceil H Hlen AC Ha0. lia.
Qed.
Theorem post_resv_fail : forall sp mem',
alloc_ceiling + AM_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WRF sp x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
ctx11 L' mem' A' ->
midrep B L' A' mem' md' /\ ama_ok A' /\ bounded A' /\ layout_le A L L' /\
(forall x, bv_unsigned a <= x < bv_unsigned a + len -> in_nonmap_region L' A' x).
Proof.
intros sp mem' Hsp FR C11.
pose proof LXs as (ER & EAr & EMt & EB & Ein & CR & Efh & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama).
pose proof len_facts as (Hlen & Hlmod & Hceil & Ha0 & Hal & RF & Hsh40). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
destruct MD' as (EV & MH & ML & MM).
destruct (ledger_like Xs LXs) as [LGs LXs'].
assert (NNs : forall k rg, region_of Xs k = Some rg -> 0 <= rg_len rg) by (intros k rg; unfold region_of; rewrite ER; apply NN).
assert (ERg' : st_regions A' = st_regions A ++ [mkRegion RkMetaRes len [] true]) by (unfold A', resv_st; cbn; rewrite ER, Esh; reflexivity).
assert (RO : forall k, region_of A' k = if (k <? N)%nat then region_of A k else if Nat.eqb k N then Some (mkRegion RkMetaRes len [] true) else None).
{ intros k. exact (region_of_new A A' _ k ERg'). }
assert (FRG := fresh_region L A md LX a len Hlen Ha0 ltac:(lia) RF).
assert (FI := fresh_img B L A md LG a len Hlen Ha0 ltac:(lia) RF).
assert (L'reg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r) by (intros r Hr; unfold L'; apply Lset_lt; exact Hr).
assert (Wdec : forall x, WRF sp x \/ ~ WRF sp x) by (intros x; unfold WRF, am_scratch, ctxW; lia).
assert (NM : forall x, bv_unsigned a <= x < bv_unsigned a + len -> in_nonmap_region L' A' x).
{ intros x Hx. split.
- exists N, (mkRegion RkMetaRes len [] true). rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl. unfold L'. rewrite Lset_new. cbn. repeat split; try discriminate; lia.
- intros (k & rg2 & Hk2 & Hl2 & Hkd2 & Hx2). rewrite RO in Hk2. destruct (Nat.ltb_spec k N).
+ rewrite (L'reg k H) in Hx2. apply (FRG k rg2 x Hk2 Hl2); [|exact Hx]. unfold reg_lo. rewrite Hkd2. lia.
+ destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk2 as <-. discriminate. }
assert (LGX : ledger_ok B L' A' md' /\ ledger_x L' A' md').
{ destruct (ledger_new_resv B L Xs md LGs LXs' NNs (mid_md _ _ _ _ _ MID) A' a len Hlen Hlmod PL ltac:(rewrite ER; exact ERg') ltac:(unfold A', resv_st; cbn; reflexivity)) as [G1 G2].
{ intros r p Hb. pose proof (inv_areas HI) as (_&_&_&_&_&_&Hbrk&_). destruct EB as [EB|EB]; rewrite EB in Hb; [|discriminate].
rewrite Hb in Hbrk. destruct Hbrk as (_ & rg & Hrg & _). rewrite ER. exact (region_of_lt _ _ _ Hrg). }
assert (ELs : Lset L Xs (bv_unsigned a) = L') by (unfold L', Lset; rewrite ER; reflexivity). rewrite ELs in G1, G2.
destruct (ledger_same B L' A' (mmap_none_model a (Z_to_bv 64 len) md) G1 G2 A' md' eq_refl eq_refl EV) as [G3 G4].
- rewrite ML, mmap_none_model_lazy. exact (eq_sym (proj1 (proj2 (mid_md _ _ _ _ _ MID)))).
- rewrite MM. cbn. exact (eq_sym (proj2 (proj2 (mid_md _ _ _ _ _ MID)))).
- exact (conj G3 G4). }
assert (UM : used_metas A' = used_metas A) by (unfold used_metas, A', resv_st; cbn; rewrite EMt; reflexivity).
assert (EA : st_areas A' = st_areas A ++ []) by (rewrite app_nil_r; unfold A', resv_st; cbn; exact EAr).
assert (MEMREP : memrep B L' A' mem').
{ refine (memrep_xfer B X R U L L' A A' mem mem' md HI XC AMA MID UM [] EA ltac:(intros; discriminate)
_ _ _ _ _ L'reg (WRF sp) Wdec FR _ [] _ _ _ _ _ _ _ _ _).
- rewrite EA, app_nil_r. exact (proj1 (inv_areas HI)).
- intros k rg Hk Hl Hkd. rewrite RO in Hk. destruct (Nat.ltb_spec k N); [exact Hk|]. destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate.
- intros k rg Hk Hl Hkd. rewrite RO. destruct (Nat.ltb_spec k N); [exact Hk | pose proof (region_of_lt _ _ _ Hk); unfold N in *; lia].
- reflexivity.
- reflexivity.
- intros x k rg [Hs|[Hc|Ha]] Hk Hl Hkd; [exact (scratch_not_region sp x k rg Hsp Hs Hk Hl) | exact (ctxW_not_region x k rg Hc Hk Hl) |].
intros Hx. apply (FRG k rg x Hk Hl); [|exact Ha]. unfold reg_lo. rewrite Hkd. lia.
- intros x a' [Hs|[Hc|Ha]] Ha' Hx; exfalso; [exact (scratch_not_area sp x a' Hsp Hs Ha' Hx) | exact (ctxW_not_area x a' Hc Ha' Hx) |].
pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas a' Ha') as (r & o & rg & Ea' & Ho & Hlo & Hr & Hl & Hl2 & _).
apply (FRG r rg x Hr Hl); [|exact Ha]. rewrite Ea' in Hx. unfold ptr_addr in Hx. cbn in Hx. unfold reg_lo. destruct (rg_kind rg); unfold PGSZ in *; lia.
- intros x a' [Hs|[Hc|Ha]] Ha' Hx; exfalso; [exact (scratch_not_area sp x a' Hsp Hs Ha' Hx) | exact (ctxW_not_area x a' Hc Ha' Hx) |].
pose proof (inv_areas HI) as (_ & Hareas & _). destruct (Hareas a' Ha') as (r & o & rg & Ea' & Ho & Hlo & Hr & Hl & Hl2 & _).
apply (FRG r rg x Hr Hl); [|exact Ha]. rewrite Ea' in Hx. unfold ptr_addr in Hx. cbn in Hx. unfold reg_lo. destruct (rg_kind rg); unfold PGSZ in *; lia.
- intros q [].
- intros q [].
- intros a' k _ _ _. unfold MT, A', resv_st. cbn. rewrite EMt. reflexivity.
- intros; discriminate.
- intros; discriminate.
- intros; discriminate.
- apply (CTX_std L' mem' A' (WRF sp) (mid_ctx _ _ _ _ _ MID) C11 ltac:(unfold A', resv_st, ctx_rest_same in *; cbn; exact CR)).
intros x [Hs|[Hc|Ha]] Hcx; [| exact Hc |].
+ exfalso. destruct Hs as [Hs|Hs]; [pose proof (so_ctx_hi _ SO); unfold AM_STACK in *; lia | exact (ENC x Hs Hcx)].
+ exfalso. apply (FI x); [apply (so_ctx_img _ SO); exact Hcx | exact Ha]. }
split; [|split; [|split; [|split]]].
- split.
+ exact SO.
+ exact MEMREP.
+ apply (tail_geom_xfer B X R U L L' A A' mem md HI XC MID UM); [| reflexivity | exact L'reg].
intros k rg Hk Hl Hkd. rewrite RO. destruct (Nat.ltb_spec k N); [exact Hk | pose proof (region_of_lt _ _ _ Hk); unfold N in *; lia].
+ apply (statics_xfer B mem mem' (WRF sp) SO (mid_statics _ _ _ _ _ MID) FR).
intros x Hst [Hs|[Hc|Ha]].
* destruct Hs as [Hs|Hs]; [| exact (ENS x Hs Hst)]. pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hst)). unfold AM_STACK in *. lia.
* apply (SNC x Hst). unfold ctxW, CTX_SIZE in *. lia.
* exact (FI x (so_statics_img _ SO x Hst) Ha).
+ exact (proj1 LGX).
+ exact (proj2 LGX).
+ refine (layout_ok_xfer B X R U L L' A A' mem md HI MID [] EA ltac:(intros; discriminate) _ _ eq_refl L'reg _ _ _ _ _).
* intros k rg Hk Hl Hkd. rewrite RO in Hk. destruct (Nat.ltb_spec k N); [exact Hk|]. destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate.
* intros k rg Hk Hl Hkd. rewrite RO. destruct (Nat.ltb_spec k N); [exact Hk | pose proof (region_of_lt _ _ _ Hk); unfold N in *; lia].
* rewrite ERg', length_app. cbn. lia.
* intros; discriminate.
* intros; discriminate.
* intros k rg Hk H'. rewrite RO in H'. destruct (Nat.ltb_spec k N); [lia|]. destruct (Nat.eqb_spec k N); [|discriminate]. subst k. unfold L'. rewrite Lset_new. intros _. exact Hal.
* intros k rg' Hk H' Hl. rewrite RO in H'. destruct (Nat.ltb_spec k N); [| unfold N in *; lia]. exists rg'. auto.
+ cbn. exact (mid_ctx _ _ _ _ _ MID).
+ cbn. exact (mid_sec _ _ _ _ _ MID).
+ exact (conj MH (conj ML MM)).
- unfold ama_ok. unfold A', resv_st. cbn -[Nat.lt]. rewrite ER, length_app. cbn. intros _. lia.
- destruct BND as (B1 & B2 & B3). unfold bounded, usage_of in *. destruct CR as (_&_&_&EU&_).
unfold A', resv_st. cbn -[Z.pow Z.le Z.lt Z.add Z.of_nat]. rewrite EU, Esh, EAr. repeat split; try apply B1; lia.
- unfold layout_le, L'. cbn. repeat split. intros r Hr. apply Lset_lt. exact Hr.
- exact NM.
Qed.
End e0.
End t.
End n.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
