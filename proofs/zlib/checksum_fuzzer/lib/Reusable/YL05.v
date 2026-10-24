(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0o YK0s YK15 YM06 YM02 YP0m YP0e YP09 YP0l YP0k YP06 YP03 YP08 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL0d YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma regs_atoms_lt_upd : forall k sr n e,
regs_atoms_lt k sr = true -> sv_atoms_lt k e = true -> regs_atoms_lt k (sr_upd sr n e) = true.
Proof.
intros k sr n e. revert sr. unfold regs_atoms_lt. induction n as [|n IH]; intros sr Hsr He.
- destruct sr as [|x t]; cbn in *; [rewrite He; reflexivity|].
apply andb_prop in Hsr as [_ Ht]. rewrite He, Ht. reflexivity.
- destruct sr as [|x t]; cbn -[sv_atoms_lt] in *.
+ rewrite (IH [] eq_refl He). reflexivity.
+ apply andb_prop in Hsr as [Hx Ht]. rewrite Hx, (IH t Ht He). reflexivity.
Qed.
Lemma regs_atoms_lt_set : forall k sr r e,
regs_atoms_lt k sr = true -> sv_atoms_lt k e = true -> regs_atoms_lt k (sr_set sr r e) = true.
Proof.
intros k sr r e Hsr He. unfold sr_set. destruct (bv_eqb r 0); [exact Hsr|]. apply regs_atoms_lt_upd; assumption.
Qed.
Lemma st_ok_xfx : forall (fx1 fx2 : FPState) segs E ss regs pc mem,
@st_ok segs fx1 E ss (@mkst fx1 regs pc mem (seg_rom segs)) ->
@st_ok segs fx2 E ss (@mkst fx2 regs pc mem (seg_rom segs)).
Proof.
intros fx1 fx2 segs E ss regs pc mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [reflexivity|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. exact H9.
Qed.
Definition static_ivl (B : malloc_syms) : ivl :=
[ (ms_lock B, ms_lock B + 4); (ms_libc B + 3, ms_libc B + 4); (ms_libc B + 8, ms_libc B + 16);
(ms_libc B + 48, ms_libc B + 56); (ms_got_guard B, ms_got_guard B + 8); (ms_guard B, ms_guard B + 8);
(ms_debruijn B - 108, ms_debruijn B + 32); (ms_size_classes B, ms_size_classes B + 96);
(ms_small_cnt B, ms_small_cnt B + 27); (ms_med_cnt B, ms_med_cnt B + 4) ].
Lemma static_ivl_sound : forall B a, in_ivl (static_ivl B) a = true -> static_owned B a.
Proof.
intros B a H. destruct (in_ivl_In _ a H) as (p & Hp & Ha). unfold static_owned. unfold static_ivl in Hp. cbn [In] in Hp.
destruct Hp as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Ha; lia.
Qed.
Definition cimg_ivl (rs : smem) : ivl :=
flat_map (fun r => match r_base r with
| None => flat_map (fun c => match c_val c with
| CImg len => [(c_off c, c_off c + len)]
| _ => []
end) (r_chunks r)
| Some _ => []
end) rs.
Lemma cimg_ivl_sound : forall segs E mem rs a,
Forall (region_ok segs E mem) rs -> in_ivl (cimg_ivl rs) a = true ->
mbyte segs mem a = seg_rom segs (Z_to_bv 64 a).
Proof.
intros segs E mem rs a HF H. destruct (in_ivl_In _ a H) as (p & Hp & Ha).
unfold cimg_ivl in Hp. apply in_flat_map in Hp as (r & Hr & Hp).
destruct (r_base r) as [n|] eqn:Hb; [destruct Hp|].
apply in_flat_map in Hp as (c & Hcin & Hp). destruct (c_val c) as [| | len |] eqn:Hcv; try (destruct Hp; fail).
destruct Hp as [<-|[]]. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) HF r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hcin) as Hck.
destruct (Hck (a - c_off c)) as (b & Hcb & Hmb).
{ unfold c_len. rewrite Hcv. cbn [cv_len]. lia. }
rewrite Hb, Hcv in *. cbn [base_val cbyte] in Hmb, Hcb. unfold img_byte in Hcb.
replace (0 + c_off c + (a - c_off c)) with a in Hmb by lia.
replace (0 + c_off c + (a - c_off c)) with a in Hcb by lia. rewrite Hmb, <- Hcb. reflexivity.
Qed.
Lemma ivl_sub1_keep : forall p f a, fst p <= a < snd p -> ~ (fst f <= a < snd f) -> in_ivl (ivl_sub1 p f) a = true.
Proof.
intros [plo phi] [flo fhi] a Hp Hf. unfold ivl_sub1, in_ivl. cbn [fst snd] in *.
destruct (Z.leb_spec fhi plo); [cbn; rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity|].
destruct (Z.leb_spec phi flo); [cbn; rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity|].
cbn [orb]. destruct (Z_lt_le_dec a flo) as [Hl|Hl].
- destruct (Z.ltb_spec plo flo); [|lia]. cbn. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- assert (Hh : fhi <= a) by lia. destruct (Z.ltb_spec fhi phi); [|lia].
rewrite existsb_app. apply orb_true_intro. right. cbn. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma ivl_sub_keep : forall l f a, in_ivl l a = true -> ~ (fst f <= a < snd f) -> in_ivl (ivl_sub l f) a = true.
Proof.
intros l f a H Hf. destruct (in_ivl_In _ a H) as (p & Hp & Ha). unfold ivl_sub, in_ivl.
apply existsb_exists. pose proof (ivl_sub1_keep p f a Ha Hf) as H1. unfold in_ivl in H1.
apply existsb_exists in H1 as (q & Hq & Hqa). exists q. split; [|exact Hqa].
apply in_flat_map. exists p. auto.
Qed.
Lemma ivl_subs_keep : forall fs l a, in_ivl l a = true -> (forall f, In f fs -> ~ (fst f <= a < snd f)) ->
in_ivl (fold_left ivl_sub fs l) a = true.
Proof.
induction fs as [|f fs IH]; intros l a H Hfs; cbn; [exact H|].
apply IH; [apply ivl_sub_keep; [exact H | apply Hfs; left; reflexivity] | intros f' Hf'; apply Hfs; right; exact Hf'].
Qed.
Definition ro_check (B : malloc_syms) (rs : smem) : bool :=
forallb (fun s => seg_writable s
|| match fold_left ivl_sub (static_ivl B ++ cimg_ivl rs)
[(Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))] with
| [] => true | _ => false end)
(ms_segs B).
Lemma ro_check_sound : forall B E mem rs,
Forall (region_ok (ms_segs B) E mem) rs -> ro_check B rs = true -> rodata_ok B mem.
Proof.
intros B E mem rs HF H a ((sg & Hin & Hw & Ha) & Hns). unfold ro_check in H.
pose proof (forallb_In _ _ sg H Hin) as Hs. cbn beta in Hs. rewrite Hw in Hs. cbn [orb] in Hs.
destruct (in_ivl (static_ivl B) a) eqn:Hst; [exfalso; exact (Hns (static_ivl_sound B a Hst))|].
destruct (in_ivl (cimg_ivl rs) a) eqn:Hci; [exact (cimg_ivl_sound (ms_segs B) E mem rs a HF Hci)|].
exfalso.
assert (K : in_ivl (fold_left ivl_sub (static_ivl B ++ cimg_ivl rs)
[(Z.of_N (seg_base sg), Z.of_N (seg_base sg) + Z.of_N (seg_size sg))]) a = true).
{ apply ivl_subs_keep.
- unfold in_ivl. cbn. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- intros f Hf Haf. apply in_app_iff in Hf as [Hf|Hf].
+ assert (X : in_ivl (static_ivl B) a = true) by (unfold in_ivl; apply existsb_exists; exists f; split; [exact Hf|];
rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity). rewrite X in Hst. discriminate.
+ assert (X : in_ivl (cimg_ivl rs) a = true) by (unfold in_ivl; apply existsb_exists; exists f; split; [exact Hf|];
rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity). rewrite X in Hci. discriminate. }
destruct (fold_left ivl_sub _ _) as [|x l]; [cbn in K; discriminate | discriminate].
Qed.
Section h.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Variables (pc_lib ra_lib empty stk : Z).
Hypothesis LIB : lib_contract_all B API pc_lib ra_lib empty stk.
Hypothesis Hstk : 0 <= stk.
Hypothesis Hfrm : frm_zero fp_csr.
Definition lib_pre_check (ss : sstate) (sp_off : Z) : bool :=
sv_eqb (sr_get (ss_regs ss) 2) (SOff 0 sp_off) &&
sv_eqb (sr_get (ss_regs ss) 4) (SLit (ms_tp B)) &&
sv_eqb (sr_get (ss_regs ss) 1) (SLit ra_lib) &&
(sp_off mod 16 =? 0) &&
match fact_of (f_atoms (ss_facts ss)) 0 with
| Some f =>
(CEIL_MIN <=? af_lo f) && (CEIL_MIN + stk <=? af_lo f + sp_off) && (af_hi f + sp_off <? 2 ^ 63) && (4 <=? af_al2 f)
| None => false
end &&
existsb (fun r => obase_eqb (r_base r) (Some 0%nat) && (r_wlo r <=? sp_off - stk) && (sp_off <=? r_whi r)) (ss_mem ss) &&
existsb (fun r => obase_eqb (r_base r) None && (r_wlo r <=? errno_addr B) && (errno_addr B + 4 <=? r_whi r)) (ss_mem ss) &&
ro_check B (ss_mem ss).
Definition lib_site_check (ss : sstate) (sp_off : Z) (keep : ivl) (blks : list (nat * Z))
(k : nat) (l1 : list (nat * YP09.region)) : bool :=
(ss_pc ss =? pc_lib) &&
match ss_resv ss with None => true | Some _ => false end &&
lib_pre_check ss sp_off &&
keep_check B keep && (errno_addr B + 4 <=? CEIL_MIN) &&
relayout_ok segs (ss_mem ss) l1 &&
ss_atoms_lt k ss && mem_atoms_lt k (map snd l1) &&
ss_atoms_lt (k + 16) (mkSS ra_lib (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss)) &&
call_frame_check (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1).
Definition lib_post_state (ss : sstate) (k : nat) (rs2 : smem) : sstate :=
mkSS ra_lib (sr_set (sr_sets (ss_regs ss) (junk_upd k caller_saved)) 10%bv (SLit 0)) rs2 None (ss_facts ss).
Lemma lib_post_frame :
forall L A regs mem md p L' A' regs' mem' md' (E : env) sp_off keep (blks : list (nat * Z)),
MR L A mem md ->
lib_post B API stk L A regs mem md p L' A' regs' mem' md' ->
keep_check B keep = true ->
errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + stk <= bv_unsigned (getr regs 2) ->
(forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\ ptr_addr L q <> p) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 -> ~ (bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off -> writable_at segs mem' a) /\
(forall a, in_ivl keep a = true ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, in_ivl [(errno_addr B, errno_addr B + 4)] a = true -> writable_at segs mem' a) /\
(forall n sz i, In (n, sz) blks -> 0 <= i < sz ->
mbyte segs mem' (bv_unsigned (ew E n) + i) = mbyte segs mem (bv_unsigned (ew E n) + i) /\
writable_at segs mem' (bv_unsigned (ew E n) + i)).
Proof.
intros L A regs mem md p L' A' regs' mem' md' E sp_off keep blks HMR0 HP Hkc Herr Hsp Hsplo Hblks.
destruct HP as (HMR' & HW' & HB' & Hid' & Ha0 & Hregs & Hvm & Hstab & Hfr & Hfri & Hbk & Hscr).
pose proof (mr_owned_low B MR LAWS) as Holow.
split; [| split; [| split; [| split]]].
- intros a Ha Ha64 Hns.
destruct (Hfr a) as [H1 H2].
+ exact (conj Ha Ha64).
+ unfold lib_scratch, spZ. rewrite Hsp. intros [Hs|Hs]; lia.
+ split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. apply Hscr. unfold lib_scratch, spZ. rewrite Hsp. left. exact Ha.
- intros a Ha. destruct (keep_check_sound B keep a Hkc Ha) as (Himg & Hlow & Hst & Hctx & Herrno).
destruct (Hfri a Himg Hst Hctx Herrno) as [H1 H2].
split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. destruct (in_ivl_In _ a Ha) as (q & Hq & Haq). destruct Hq as [<-|[]]. cbn [fst snd] in Haq.
apply Hscr. unfold lib_scratch. right. exact Haq.
- intros n sz i Hin Hi. destruct (Hblks n sz Hin) as (q & HinA & Hq & Hqp). rewrite <- Hq. split.
+ apply (Hbk q sz i HinA Hqp Hi).
+ apply present_writable. destruct (Hstab q sz HinA) as (q' & HinA' & Hstab'). rewrite <- Hstab'.
exact (proj1 (mr_blocks B MR LAWS L' A' mem' md' q' sz i HMR' HinA' Hi)).
Qed.
Lemma lib_pre_intro : forall E ss ms L A md sp_off p n,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
lib_pre_check ss sp_off = true ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 p -> getr (ms_regs ms) 11%bv = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)) ->
lib_pre B API stk empty L A (ms_regs ms) (ms_mem ms) md ra_lib p n /\
bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off /\
alloc_ceiling + stk <= bv_unsigned (getr (ms_regs ms) 2).
Proof.
intros E ss ms L A md sp_off p n HS HSA HMR HW HB Hid Hck Hp Hn Hpn.
unfold lib_pre_check in Hck.
apply andb_prop in Hck as [Hck Hro].
apply andb_prop in Hck as [Hck Herr]. apply andb_prop in Hck as [Hck Hstk']. apply andb_prop in Hck as [Hck Hf].
apply andb_prop in Hck as [Hck Hmod]. apply andb_prop in Hck as [Hck Hra]. apply andb_prop in Hck as [Hsp Htp].
apply sv_eqb_eq in Hsp. apply sv_eqb_eq in Htp. apply sv_eqb_eq in Hra. apply Z.eqb_eq in Hmod.
destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & HM & HG).
destruct (fact_of (f_atoms (ss_facts ss)) 0) as [f|] eqn:Hf0; [|discriminate].
pose proof (fact_of_sound E _ 0%nat f (proj1 HG) Hf0) as (Hlohi & Hal & Hal2).
apply andb_prop in Hf as [Hf Ha4]. apply andb_prop in Hf as [Hf Hhi]. apply andb_prop in Hf as [Hmin Hlo].
apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. apply Z.leb_le in Ha4.
pose proof (stack_anchored_sound E (ss_facts ss) 0 (af_lo f - CEIL_MIN) HSA
ltac:(unfold anch_lo; rewrite (fact_lo_of _ _ _ Hf0), Hmin; reflexivity)) as Hanc.
apply Z.leb_le in Hmin.
pose proof (mod16_of_al2 _ _ Ha4 Hal) as H16.
assert (Hac : 0 <= alloc_ceiling) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hsp2 : bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off).
{ rewrite (Hregs 2%bv), Hsp. cbn [sv_denot]. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
split; [| split; [exact Hsp2 | rewrite Hsp2; lia]].
unfold lib_pre, spZ. rewrite Hsp2.
split; [exact HMR|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hid|]. split.
{ rewrite (Hregs 1%bv), Hra. reflexivity. }
split.
{ rewrite Z.add_mod, H16, Hmod by lia. reflexivity. }
split; [lia|]. split; [lia|]. split.
{ apply existsb_In in Hstk' as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
replace a with (bv_unsigned (ew E 0%nat) + (a - bv_unsigned (ew E 0%nat))) by lia. apply Hw. lia. }
split.
{ rewrite (Hregs 4%bv), Htp. reflexivity. }
split.
{ apply existsb_In in Herr as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
replace a with (0 + a) by lia. apply Hw. lia. }
split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
exact (ro_check_sound B E (ms_mem ms) (ss_mem ss) (proj1 (proj2 HM)) Hro).
Qed.
Lemma lib_site_check_sound : forall ss sp_off keep blks k l1,
lib_site_check ss sp_off keep blks k l1 = true ->
ss_pc ss = pc_lib /\ ss_resv ss = None /\
lib_pre_check ss sp_off = true /\ keep_check B keep = true /\ errno_addr B + 4 <= alloc_ceiling /\
relayout_ok segs (ss_mem ss) l1 = true /\ ss_atoms_lt k ss = true /\ mem_atoms_lt k (map snd l1) = true /\
ss_atoms_lt (k + 16) (mkSS ra_lib (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss)) = true /\
call_frame_check (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true /\
sr_get (ss_regs ss) 1 = SLit ra_lib.
Proof.
intros ss sp_off keep blks k l1 H. unfold lib_site_check in H.
repeat match type of H with _ && _ = true => apply andb_prop in H as [H ?X] end.
apply Z.eqb_eq in H. destruct (ss_resv ss); [discriminate|]. apply Z.leb_le in X4.
assert (Hra : sr_get (ss_regs ss) 1 = SLit ra_lib).
{ unfold lib_pre_check in X6. repeat match type of X6 with _ && _ = true => apply andb_prop in X6 as [X6 ?Y] end.
apply sv_eqb_eq in Y4. exact Y4. }
pose proof YM05.alloc_ceiling_val.
repeat split; try assumption. lia.
Qed.
Theorem st_ok_after_lib :
forall k E ss regs pc mem md p L A L' A' regs' mem' md' (sp_off : Z) keep
(blks : list (nat * Z)) (l1 : list (nat * YP09.region)),
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> stack_anchored E (ss_facts ss)   ->
ss_atoms_lt k ss = true ->
MR L A mem md ->
lib_post B API stk L A regs mem md p L' A' regs' mem' md' ->
keep_check B keep = true -> errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + stk <= bv_unsigned (getr regs 2) ->
(forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\ ptr_addr L q <> p) ->
relayout_ok segs (ss_mem ss) l1 = true ->
mem_atoms_lt k (map snd l1) = true ->
call_frame_check (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true ->
sr_get (ss_regs ss) 1 = SLit ra_lib ->
st_ok segs (havoc E k (map (getr regs') caller_saved))
(lib_post_state ss k (map snd l1))
(mkst regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)).
Proof.
intros k E ss regs pc mem md p L A L' A' regs' mem' md' sp_off keep blks l1
HS HSA Hat HMR0 HP Hkc Herr Hsp Hsplo Hblks Hrl Hma Hcf Hra.
assert (HS1 : st_ok segs (havoc E k (map (getr regs') caller_saved))
(mkSS ra_lib (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss))
(mkst regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs))).
{ change (junk_upd k caller_saved) with ([] ++ junk_upd k caller_saved).
eapply (st_ok_splice_havoc segs k E ss regs regs' pc ra_lib mem mem' (map snd l1) [] caller_saved HS Hat).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hma.
- cbn [map fst app]. apply regs_preserved_frame. destruct HP as (_ & _ & _ & _ & _ & Hregs & _). exact Hregs.
- constructor.
- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & HG). cbn [ms_mem mkst] in HM.
destruct (lib_post_frame L A regs mem md p L' A' regs' mem' md' E sp_off keep blks
HMR0 HP Hkc Herr Hsp Hsplo Hblks) as (F1 & F2 & F3 & F5 & F4).
apply (mem_ok_call_frame segs (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks E mem mem' F1 F2 F3 F5 F4 HG HSA).
+ eapply mem_ok_relayout; [exact HM | exact Hrl].
+ exact Hcf. }
unfold lib_post_state. apply (st_ok_regs segs _ _ _ _ HS1).
cbn [ss_regs]. intros r. destruct (decide (r = 10%bv)) as [->|Hne].
- rewrite sr_get_set_same by reflexivity.
destruct HS1 as (_ & _ & _ & _ & _ & _ & Hregs1 & _). rewrite <- (Hregs1 10%bv). cbn [ms_regs mkst].
destruct HP as (_ & _ & _ & _ & Ha0 & _). rewrite Ha0. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Theorem lib_site : forall E ss ms md L A p n sp_off keep blks k l1 rs2 T,
st_ok segs E ss ms -> stack_anchored E (ss_facts ss)   ->
lib_site_check ss sp_off keep blks k l1 = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 p -> getr (ms_regs ms) 11%bv = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ ptr_addr L q <> p) ->
(forall (fx' : FPState) A' L' ms' md' g,
@st_ok segs fx' (post_env E k (ms_regs ms') g) (mkSS ra_lib (ss_regs (lib_post_state ss k rs2)) rs2 None (ss_facts ss)) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss)   ->
frm_zero (@fp_csr fx') ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' -> st_init_done A' = true ->
(exists vm', md' = with_vmmaps vm' md) ->
(forall q sz, In (q, sz) (user_blocks A) -> exists q', In (q', sz) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg ms md) T.
Proof.
intros E ss ms md L A p n sp_off keep blks k l1 rs2 T HS HSA Hck Hrs2 HMR HW HB Hid Hp Hn Hpn Hblks HK.
destruct (lib_site_check_sound _ _ _ _ _ _ Hck) as (Hpc & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf & Hra).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (lib_pre_intro E ss ms L A md sp_off p n HS HSA HMR HW HB Hid Hcp Hp Hn Hpn) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
apply (SR_realizes segs _ _ T (LIB fx L A (ms_regs ms) (ms_mem ms) md p n Hpre Hfrm)).
intros c' (fx' & L' & A' & regs' & mem' & md' & -> & Hfrm' & Hpost).
pose proof Hpost as (HMR' & HW' & HB' & Hid' & Ha0 & Hregs & Hvm & Hstab & Hfr & Hfri & Hbk & Hscr).
assert (HS1 := st_ok_after_lib k E ss (ms_regs ms) _ (ms_mem ms) md p L A L' A' regs' mem' md'
sp_off keep blks l1 HS HSA Hat HMR Hpost Hkc Herr Hsp Hsplo Hblks Hrl Hma Hcf Hra).
unfold drv_add_statics in Hrs2.
destruct (abs_region_index (map snd l1) (ms_got_guard B) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_libc B + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_guard B) 0) as [i3|]; [|discriminate].
assert (Hat3 : ss_atoms_lt (k + 16) (lib_post_state ss k (map snd l1)) = true).
{ unfold lib_post_state. unfold ss_atoms_lt in Hat2 |- *. cbn [ss_regs ss_mem ss_facts ss_resv] in Hat2 |- *.
apply andb_prop in Hat2 as [Hat2 _]. apply andb_prop in Hat2 as [Hat2 HF']. apply andb_prop in Hat2 as [HR' HM'].
rewrite (regs_atoms_lt_set (k + 16) _ 10%bv (SLit 0) HR' eq_refl), HM', HF'. reflexivity. }
apply (st_ok_xfx fx fx') in HS1.
destruct (st_ok_statics B MR AX _ _ (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) L' A' md' (k + 16) i1 i2 i3 rs2
HS1 HMR' Hat3 Hrs2) as (g & Hg01 & HS2).
apply (HK fx' A' L' (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) md' g).
- exact HS2.
- apply (stack_anchored_agree_ss k E _ ss (post_env_agree E k regs' g) Hat HSA).
- exact Hfrm'.
- exact HMR'.
- exact HW'.
- exact HB'.
- exact Hid'.
- exact Hvm.
- exact Hstab.
- cbn [ms_mem mkst]. intros a Ha Ha64 Hns.
destruct (lib_post_frame L A (ms_regs ms) (ms_mem ms) md p L' A' regs' mem' md' E sp_off keep blks
HMR Hpost Hkc Herr Hsp Hsplo Hblks) as (F1 & _).
exact (proj1 (F1 a Ha Ha64 Hns)).
- cbn [ms_mem mkst]. exact Hbk.
Qed.
End h.
End d.
