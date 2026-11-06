From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0i YO0f YO0d YO0u YO10 YN03 YN2b.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma NoDup_map_on {X Y} (f : X -> Y) : forall l,
List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof using.
induction l as [|a t IH]; intros N H; cbn; [constructor|].
inversion N as [|a' t' Ha Ht]; subst. constructor.
- intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply Ha.
rewrite (H a y (or_introl eq_refl) (or_intror Hy) (eq_sym E)). exact Hy.
- apply IH; [exact Ht|]. intros x y Hx Hy. apply H; right; assumption.
Qed.
Lemma user_block_strict : forall A p n, WF A -> In (p, n) (user_blocks A) ->
exists rg, region_of A (prid p) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff p /\ 0 <= n /\ poff p + n + IB <= rg_len rg.
Proof using.
intros A p n HW Hin.
destruct (in_user_blocks_inv A (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
injection E as -> ->.
apply (used_metas_usedX A g am HW) in Hg.
destruct (used_group_region [] None U0 A g am HW Hg) as (rg & R & K & Lv & O & Ext & _).
pose proof (block_in_slot A g am i fr HW Hg Hi Hfr) as (B1 & B2 & B3).
pose proof (slot_in_span [] None U0 A HW g am i Hg Hi) as [S1 S2].
exists rg. unfold frame_ptr, slot_start in *. destruct (am_mem am) as [k o]. cbn [padd prid poff] in *.
split; [exact R|]. split; [exact K|]. split; [exact Lv|]. unfold IB, UNIT in *. lia.
Qed.
Lemma user_block_addr_inj : forall L A p n q m, WF A -> layout_ok L A ->
In (p, n) (user_blocks A) -> In (q, m) (user_blocks A) -> ptr_addr L p = ptr_addr L q -> p = q.
Proof using.
intros L A p n q m HW HL Hp Hq E. destruct HL as (_ & _ & PW & _).
destruct (user_block_strict A p n HW Hp) as (rp & Rp & Kp & Lp & Op & Np & Mp).
destruct (user_block_strict A q m HW Hq) as (rq & Rq & Kq & Lq & Oq & Nq & Mq).
destruct p as [kp op], q as [kq oq]. cbn [prid poff] in *. cbv [ptr_addr loc_addr] in E.
destruct (Nat.eq_dec kp kq) as [<-|Hne]; [f_equal; lia|]. exfalso.
pose proof (footprint_region_In A _ _ Rp Kp Lp) as Ip. pose proof (footprint_region_In A _ _ Rq Kq Lq) as Iq.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW Ip Iq
ltac:(intros X; apply Hne; injection X; intros; assumption)) as [D|D];
cbv [ranges_disjoint crange loc_addr fst snd] in D; unfold IB in *; lia.
Qed.
Lemma MRc_blocks_nodup : forall B L A mem md, MRc B L A mem md -> List.NoDup (map fst (blocks L A)).
Proof using.
intros B L A mem md HM. pose proof (mc_wf _ _ _ _ _ HM) as HW. pose proof (mc_layout _ _ _ _ _ HM) as HL.
replace (map fst (blocks L A)) with (map (ptr_addr L) (map fst (user_blocks A)))
by (unfold blocks; rewrite !map_map; reflexivity).
apply NoDup_map_on; [exact (user_block_ptrs_NoDup A HW)|].
intros x y Hx Hy E. apply in_map_iff in Hx as ([p n] & <- & Hp). apply in_map_iff in Hy as ([q m] & <- & Hq).
exact (user_block_addr_inj L A p n q m HW HL Hp Hq E).
Qed.
Section c.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Theorem blocks_nodup_ok : (forall L A mem md, MR L A mem md -> MRx B L A mem md) -> blocks_nodup B API.
Proof using.
intros HX L A mem md HM. apply (proj2 (stdpp.base.NoDup_ListNoDup _)).
exact (MRc_blocks_nodup B L A mem md (MRx_MRc B L A mem md (HX L A mem md HM))).
Qed.
End c.
End a.
