(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l.Mq0.

Local Ltac Z.euclidean_division_equations_cleanup ::= zify_cheap_cleanup. Local Ltac mkr__euclidean_division_equations_cleanup_0 := zify_cheap_cleanup.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid. Local Ltac mkr__zify_internal_to_euclidean_division_equations_1 := zify_fast_euclid.
Local Ltac lia ::= lia_tuned. Local Ltac mkr__lia_2 := lia_tuned.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqRD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqRD.

Local Instance asanreflect_fx : QqRD.FPState := QqRD.fx0.
Import ListNotations.
Open Scope bv_scope.

Definition mrestrict (H : word -> bool) (m : word -> option byte)
: word -> option byte :=
fun a => if H a then None else m a.

Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
: word -> option byte :=
fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
{| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
ms_pc_val := ms_pc_val ms;
ms_svc_pending := ms_svc_pending ms;
ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
ms_mem := mrestrict H (ms_mem ms);
ms_rom := ms_rom ms |}.

Definition unrestrict (H : word -> bool) (full : word -> option byte)
(ms' : machine_state) : machine_state :=
{| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
ms_pc_val := ms_pc_val ms';
ms_svc_pending := ms_svc_pending ms';
ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
ms_mem := munrestrict H full (ms_mem ms');
ms_rom := ms_rom ms' |}.

Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

Definition wx_segs_nowrap (segs : list Segment) : Prop :=
forall seg, In seg segs ->
seg_executable seg && seg_writable seg = true ->
(Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

Definition woff (a : word) (k : nat) : word :=
Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
forall a n, In (a, n) l -> range_avoids H a n.

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : forall H a n,
range_avoids H a (S n) -> H a = false.
Proof.
intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
intros H a n H0 Hr k Hk. destruct k as [|k].
- rewrite woff_0. exact H0.
- rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : forall H a n l,
range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
intros H a n l Ha Hl a' n' [Heq | Hin].
- injection Heq as <- <-. exact Ha.
- exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : forall H l1 l2,
ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
[exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

Lemma restrict_svc_pending : forall H ms,
ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.

Lemma unrestrict_mem : forall H full ms,
ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.

Lemma munrestrict_mrestrict : forall H m,
munrestrict H m (mrestrict H m) = m.
Proof.
intros H m. apply functional_extensionality. intro a.
unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : forall H full m,
mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
intros H full m. apply functional_extensionality. intro a.
unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma restrict_unrestrict : forall H full ms,
restrict H (unrestrict H full ms) = restrict H ms.
Proof.
intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
rewrite mrestrict_munrestrict. reflexivity.
Qed.

Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
apply functional_extensionality. intro a. unfold mrestrict.
destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
ov_read_bytes segs (mrestrict H m) a n = Some bs ->
ov_read_bytes segs m a n = Some bs /\ range_avoids H a n.
Proof.
induction n as [|n IH]; intros m a bs Hr.
- cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
- cbn [ov_read_bytes] in Hr |- *.
unfold mrestrict in Hr at 1.
destruct (H a) eqn:Ha.
+ rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
+ destruct (match m a with
| Some b => Some b
| None => match memory_read segs a 1 with
| Some (b :: _) => Some b | _ => None end
end) as [b|]; [|discriminate].
destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
[|discriminate].
destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
rewrite Hfull. split; [exact Hr|].
apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : forall m a,
wview segs (mrestrict H m) a =
if H a then None else wview segs m a.
Proof.
intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : forall n m a,
store_ok segs (mrestrict H m) a n = true ->
store_ok segs m a n = true /\ range_avoids H a n.
Proof.
induction n as [|n IH]; intros m a Hs.
- split; [reflexivity | intros k Hk; lia].
- cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
destruct (H a) eqn:Ha; [discriminate|].
destruct (wview segs m a) as [b|]; [|discriminate].
destruct (IH m (a + 1) Hs) as [Hfull Hav].
split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

Lemma write_to_mem_restrict : forall bs m a,
range_avoids H a (length bs) ->
write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs).
Proof.
induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
cbn [write_to_mem length] in *.
pose proof (range_avoids_hd H a _ Hav) as Ha.
pose proof (range_avoids_tl H a _ Hav) as Htl.
rewrite <- (IH _ (a + 1) Htl). f_equal.
apply functional_extensionality. intro x. unfold mrestrict.
destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall bs m a x,
range_avoids H a (length bs) -> H x = true ->
write_to_mem m a bs x = m x.
Proof.
induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
cbn [write_to_mem length] in *.
pose proof (range_avoids_hd H a _ Hav) as Ha.
pose proof (range_avoids_tl H a _ Hav) as Htl.
rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
rewrite Ha in Hx. discriminate.
Qed.

Lemma find_segment_some_spec : forall l addr n seg,
find_segment l addr n = Some seg ->
In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
/\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
cbn [find_segment] in Hf.
destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
- injection Hf as ->. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2.
split; [left; reflexivity | split; assumption].
- destruct (IH addr n seg Hf) as (Hin & H1 & H2).
split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : forall l addr n,
find_segment l addr n = None ->
forall seg, In seg l ->
~ ((Z.of_N (seg_base seg) <= addr)%Z
/\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
cbn [find_segment] in Hf.
destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
[discriminate|].
destruct Hin as [<- | Hin].
- intros [H1 H2]. apply andb_false_iff in E as [E | E].
+ apply Z.leb_gt in E. lia.
+ apply Z.leb_gt in E. lia.
- exact (IH addr n Hf seg Hin).
Qed.

Lemma in_segment_not_hidden : forall (x : word) seg,
In seg segs ->
(Z.of_N (seg_base seg) <= bv_unsigned x)%Z ->
(bv_unsigned x + 1 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
H x = false.
Proof.
intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
In seg segs ->
(Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
(Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z ->
seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
cbn [seg_ov_read_bytes].
assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
unfold mrestrict at 1. rewrite Ha.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
{ rewrite bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
pose proof (bv_unsigned_in_range 64 a). lia. }
rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
intros m a n. unfold code_read_ov.
destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
interp_eff_accesses segs t (mrestrict H m)
= MachineOk (@mkAccessReport _ (c, mr') rs) ->
exists mf',
interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
/\ mr' = mrestrict H mf'
/\ (forall x, H x = true -> mf' x = m x)
/\ ranges_avoid H rs.
Proof.
induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
try discriminate.
-
injection Hi as <- <- <-. exists m.
split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
apply ranges_avoid_nil.
-
destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
[|discriminate].
destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
rewrite Hfull.
destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
rewrite Hint. cbn [access_value accessed_ranges].
exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
apply ranges_avoid_cons; assumption.
-
destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
by apply length_Z_to_le_bytes.
rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
in Hi by (rewrite Hlen; exact Hav).
destruct (interp_eff_accesses segs k
(mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
rewrite Hint. cbn [access_value accessed_ranges].
exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
+ intros x Hx. rewrite (Hhid x Hx).
apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
+ apply ranges_avoid_cons; assumption.
Qed.

Lemma decode_exec_accesses_restrict : forall ms w msr' rs',
decode_exec_accesses segs (restrict H ms) w
= MachineOk (@mkAccessReport _ msr' rs') ->
decode_exec_accesses segs ms w
= MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
/\ ranges_avoid H rs'
/\ hclean H msr'.
Proof.
intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
destruct (is_ecall w) eqn:Hec.
- injection Hd as <- <-.
split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
rewrite munrestrict_mrestrict. destruct ms; reflexivity.
- destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
destruct (interp_eff_accesses segs
(exec (Z_to_bv 64 isz) i
{| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
c_resv := ms_resv ms |})
(mrestrict H (ms_mem ms)))
as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
as (mf' & Hfull & -> & Hhid & Hrs).
rewrite Hfull. cbn [access_value accessed_ranges].
split; [|split; [exact Hrs|]].
+ unfold unrestrict. cbn.
replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
+ intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : forall ms msr' rs',
step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs') ->
step_accesses segs ms
= MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
/\ ranges_avoid H rs'
/\ hclean H msr'.
Proof.
intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
destruct (fetch_word segs (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
{ exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
exfalso. unfold fetch_failure in Hs.
destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
|| match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
| Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
| None => false end); discriminate.
Qed.

Theorem step_restrict_sound : forall ms msr',
RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
exists rep,
step_accesses segs ms = MachineOk rep
/\ access_value _ rep = unrestrict H (ms_mem ms) msr'
/\ ranges_avoid H (accessed_ranges _ rep)
/\ hclean H msr'
/\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
Proof.
intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
injection Hs as ->.
destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
apply restrict_unrestrict_clean. exact Hcl.
Qed.

Corollary step_restrict_step : forall ms msr',
RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
RiscvSemantics.step segs ms = MachineOk (unrestrict H (ms_mem ms) msr').
Proof.
intros ms msr' Hs.
destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.

End ISA.

Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
&& (bv_unsigned p + page_size <=? snd iv)%Z) A.

Definition A_wf (A : list (Z * Z)) : Prop :=
Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
/\ (snd iv) mod page_size = 0)%Z A.

Fixpoint A_bytes (A : list (Z * Z)) : Z :=
match A with
| [] => 0
| iv :: r => (snd iv - fst iv) + A_bytes r
end%Z.

Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
(A : list (Z * Z)) : Prop :=
forall w : word,
page_in_ranges (page_base w) lazy = true -> H w = false ->
page_allowedb A (page_base w) = true.

Definition eager_used (m : Model) : Z :=
live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
minv_nodup    : List.NoDup (m_vm_materialized m);
minv_aligned  : forall p, In p (m_vm_materialized m) ->
(bv_unsigned p mod page_size = 0)%Z;
minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
minv_lazy     : forall p, In p (m_vm_materialized m) ->
page_in_ranges p (m_vm_lazy m) = true;
minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

Definition same_but_materialized (m m' : Model) : Prop :=
m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Fixpoint A_pages (A : list (Z * Z)) : list Z :=
match A with
| [] => []
| iv :: r =>
map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
(seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
++ A_pages r
end.

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

Lemma page_base_woff : forall a k,
page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
intros a k. unfold page_base, woff, page_base_of.
set (z := (bv_unsigned a + Z.of_nat k)%Z).
pose proof (bv_unsigned_in_range 64 a) as Ha.
assert (Hz : (0 <= z)%Z) by (unfold z; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite !two64_as_pages.
set (r := (z mod (page_size * 2 ^ 52))%Z).
assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).

pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
fold r in Hdm.
set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
{ rewrite Hdm at 1.
replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
rewrite Z.div_add by lia. lia. }
rewrite Hfl.
replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma page_insert_nodup : forall p pages,
List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
intros p pages Hnd. unfold page_insert.
destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
constructor; [|exact Hnd].
intros Hin. unfold page_mem in Hm.
assert (Ht : existsb (bv_eqb p) pages = true).
{ apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
intros p q pages Hin. unfold page_insert in Hin.
destruct (page_mem q pages); [right; exact Hin|].
destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
In p (access_pages_acc base n pages) ->
In p pages
\/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
- left; exact Hin.
- destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
+ destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
* right. exists 0%nat. split; [lia|]. f_equal. lia.
* left; exact Hin''.
+ right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
In p (accesses_pages accs pages) ->
In p pages
\/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
- left; exact Hin.
- destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
+ destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
* left; exact Hp.
* right. exists a, n, k. split; [left; reflexivity | split; assumption].
+ right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

Lemma with_vm_backing_id : forall m,
with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep_cfg segs (alloc_only_cfg false) c (evs i) (SNext (nx i)))
/\ (forall e st, sstep_cfg segs (alloc_only_cfg false) c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma sstep_instr_det : forall ms model ms1 model1 e st,
ms_svc_pending ms = None ->
mi_account_step segs ms model = MachineOk (ms1, model1) ->
sstep segs (mkCfg ms model) e st ->
e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
intros ms model ms1 model1 e st Hsvc Hacc Hss.
inversion Hss; subst;
match goal with
| Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
| Ha : mi_account_step segs ms model = _ |- _ =>
rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
end.
Qed.

Lemma step_hclean : forall ms ms',
hclean H ms ->
RiscvSemantics.step segs ms = MachineOk ms' ->
hclean H ms'.
Proof.
intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
exact Hcl.
Qed.

Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

End Nodes.

Lemma materialize_model_accesses_nil : forall m,
materialize_model_accesses m [] = Some m.
Proof.
intros m. unfold materialize_model_accesses, materialize_accesses.
unfold newly_materialized_pages. cbn [accesses_pages List.filter].
rewrite with_vm_backing_id. reflexivity.
Qed.

Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
match materialize_model_accesses m accs with
| Some m' => m'
| None => m
end.

Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.

End SyscallNode.

Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Definition seg_top (seg : Segment) : Z :=
(Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
forallb (fun seg => negb (seg_executable seg && seg_writable seg)
|| (seg_top seg <=? 2 ^ 64)%Z) segs.

Lemma wx_segs_nowrap_of_b : forall segs,
wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
apply Z.leb_le in Hb. exact Hb.
Qed.

Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
forallb (fun seg => (seg_top seg <=? top)%Z) segs.

Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

