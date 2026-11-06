(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgSiteA.v at ea8335784b52 for image B
   (fuzz_rate.asan-ubsan): image B's record RtPgImgB.rate_himg_B and its lists rate_B_L23_tl / rate_B_L56_tl /
   rate_B_strs / rate_B_i32 / rate_B_u64 / rate_B_globs in place of image A's; the names rate_A_X become rate_B_X;
   image A's check_csv stack bound and its segment-start string lemma are left out (image B states the bound as
   RtPgImgB.T_csv_STK_B, and its segment-start strings in the checks' shared layer). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14): the call-site lemmas of rule 1j-bis for the
   texts of lib/A/RtPgCSpec.v, at the states those texts already state (the segment contracts' starts and ends, with
   image B's record RtPgImgB.rate_himg_B). Each lemma shows that the stated state supplies a premise of the next
   call's contract. Proves no function (kind: statement text).
   - rate_B_site_malloc_pod: at C2 (0x82a2c, rate_build_contract's end) a0 = len + (len == 0) = len, and
     8 <= len <= 5440 < MALLOC_MAX: the request premise `0 <= n < MALLOC_MAX` of the allocator's contract
     (lib/Reusable/YG0d.v amalloc_realizes) and the pod size rate_check_contract reads.
   - rate_B_site_malloc_buf: at C5 (0x82fac) a0 = buflen + (buflen == 0) in [1, 23] < MALLOC_MAX, the request and
     the buf size rate_csv_contract reads.
   - rate_B_site_cut3 / rate_B_site_cut6: at C3 (0x82a30) and C6 (0x82fb0) the start values of
     rate_check_contract / rate_csv_contract hold when the malloc call kept every location of the cut list but a0,
     which holds the block.
   - after a call that lets runtime-owned bytes change: rate_B_img_facts (RtPgCSpec.rt_img_facts at image B) and the
     lemmas that rebuild a string or table premise at the state after such a call from the one before it:
     rate_B_{str,i32,u64}_glob, rate_B_{str,i32,u64}_unowned, rate_B_cstr_at, rate_B_i32tab_at, rate_B_u64tab_at. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK04 YA0n YI04 YP09 YG0v YG00 YG0f YG0n YG0d YCbq YC5d YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Spa Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB.
Import ListNotations.
Local Open Scope Z_scope.

(* ===================== C2 and C5: the two malloc requests ===================== *)
Lemma rate_B_site_malloc_pod : forall (e : rt_renv) (rest : list byte), q_len e = rt_len rest ->
rt_xv e XLenNZ = q_len e /\ 8 <= q_len e <= 5440 /\ 0 <= rt_xv e XLenNZ < MALLOC_MAX.
Proof.
intros e rest He. pose proof (rt_len_bounds rest) as Hb. rewrite <- He in Hb. cbn [rt_xv].
destruct (Z.eqb_spec (q_len e) 0) as [E0|E0]; [lia|].
unfold MALLOC_MAX. lia.
Qed.

Lemma rate_B_site_malloc_buf : forall (e : rt_renv), rt_hdr_ok e ->
rt_xv e XBl = rt_bl (q_buflen e) /\ 1 <= rt_bl (q_buflen e) <= 23 /\ 0 <= rt_xv e XBl < MALLOC_MAX.
Proof.
intros e He. destruct He as (_ & _ & Hb & _). cbn [rt_xv]. unfold rt_bl.
destruct (Z.eqb_spec (q_buflen e) 0) as [E0|E0]; unfold MALLOC_MAX; lia.
Qed.

(* ===================== C3 and C6: the values after a malloc returns ===================== *)
Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma rate_B_site_cut3 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rt_renv),
rt_cut segs H mem regs e (hi_L2 rate_himg_B) ->
getr regs' (Z_to_bv 5 10) = w64 (q_pod e) ->
(forall r, In (LReg r) (map fst rate_B_L23_tl) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o, In (LCell b o) (map fst rate_B_L23_tl) -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (rt_xv e b + o + i) = mbyte segs (mrestrict H mem) (rt_xv e b + o + i)) ->
rt_cut segs H mem' regs' e (hi_L3 rate_himg_B).
Proof.
intros H mem mem' regs regs' e HC H10 Hr Hc.
unfold rt_cut in HC |- *.
change (hi_L2 rate_himg_B) with ((LReg 10, XLenNZ) :: rate_B_L23_tl) in HC.
change (hi_L3 rate_himg_B) with ((LReg 10, XPod) :: rate_B_L23_tl).
rewrite Forall_cons_iff in HC. destruct HC as [_ HC].
apply Forall_cons.
- cbn [fst snd rt_at rt_xv]. exact H10.
- exact (rt_cut_keep segs H mem mem' regs regs' e rate_B_L23_tl HC Hr Hc).
Qed.

Lemma rate_B_site_cut6 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rt_renv),
rt_cut segs H mem regs e (hi_L5 rate_himg_B) ->
getr regs' (Z_to_bv 5 10) = w64 (q_buf e) ->
(forall r, In (LReg r) (map fst rate_B_L56_tl) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o, In (LCell b o) (map fst rate_B_L56_tl) -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (rt_xv e b + o + i) = mbyte segs (mrestrict H mem) (rt_xv e b + o + i)) ->
rt_cut segs H mem' regs' e (hi_L6 rate_himg_B).
Proof.
intros H mem mem' regs regs' e HC H10 Hr Hc.
unfold rt_cut in HC |- *.
change (hi_L5 rate_himg_B) with ((LReg 10, XBl) :: rate_B_L56_tl) in HC.
change (hi_L6 rate_himg_B) with ((LReg 10, XBuf) :: rate_B_L56_tl).
rewrite Forall_cons_iff in HC. destruct HC as [_ HC].
apply Forall_cons.
- cbn [fst snd rt_at rt_xv]. exact H10.
- exact (rt_cut_keep segs H mem mem' regs regs' e rate_B_L56_tl HC Hr Hc).
Qed.
End c3.

(* ============ after a call that lets runtime-owned bytes change: image B's read-only facts ============
   RtPgCSpec.rt_img_facts at image B's record and range [IMG_LO, IMG_TOP) = [0x10000, 0x5fa000)
   (lib/Reusable/YImgTop.v): the hypothesis image B's walks take, with AR_laws, to re-derive a string, table or cell
   fact after a malloc, a side-stack frame or an rt_cpost_o call (reac_rate_drivable_csv's format, separators and
   ordered after its class-1 frame; check_csv's closed_list after its class-2 frame; the main walk's after
   reac_rate_drivable_csv returns and after each malloc). Image B's close proves it at its symbol record. Below: each
   string and table of the record is a registered global of hi_globs with room for it (each string also 64 bytes
   inside the range, for its shadow hull; the tables' predicates read no hull), and its bytes are no owned static, so
   RtPgBase.rt_img_unowned and rt_cstr_at / rt_i32tab_at / rt_u64tab_at apply. *)
Definition rate_B_marked_chk : bool :=
  forallb (fun s => existsb (fun g => (fst g =? fst s) && (Z.of_nat (length (snd s)) + 1 <=? snd g)) rate_B_globs &&
                    (IMG_LO + 64 <=? fst s) && (fst s + Z.of_nat (length (snd s)) + 1 + 64 <=? IMG_TOP)) rate_B_strs &&
  forallb (fun t => existsb (fun g => (fst g =? fst t) && (4 * Z.of_nat (length (snd t)) <=? snd g)) rate_B_globs)
    rate_B_i32 &&
  forallb (fun t => existsb (fun g => (fst g =? fst t) && (8 * Z.of_nat (length (snd t)) <=? snd g)) rate_B_globs)
    rate_B_u64.
Lemma rate_B_marked_chk_ok : rate_B_marked_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_B_str_glob : forall a s, In (a, s) rate_B_strs ->
  (exists sz, In (a, sz) rate_B_globs /\ Z.of_nat (length s) + 1 <= sz) /\
  IMG_LO + 64 <= a /\ a + Z.of_nat (length s) + 1 + 64 <= IMG_TOP.
Proof.
intros a s Hin. pose proof rate_B_marked_chk_ok as E. unfold rate_B_marked_chk in E.
apply andb_true_iff in E. destruct E as [E _]. apply andb_true_iff in E. destruct E as [E _].
rewrite forallb_forall in E. specialize (E (a, s) Hin). cbv beta in E. cbn [fst snd] in E.
apply andb_true_iff in E. destruct E as [E Hhi]. apply andb_true_iff in E. destruct E as [Ex Hlo].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
split; [exact (rt_glob_of_b a _ rate_B_globs Ex)|]. split; [exact Hlo | exact Hhi].
Qed.
Lemma rate_B_i32_glob : forall t vs, In (t, vs) rate_B_i32 ->
  exists sz, In (t, sz) rate_B_globs /\ 4 * Z.of_nat (length vs) <= sz.
Proof.
intros t vs Hin. pose proof rate_B_marked_chk_ok as E. unfold rate_B_marked_chk in E.
apply andb_true_iff in E. destruct E as [E _]. apply andb_true_iff in E. destruct E as [_ E].
rewrite forallb_forall in E. specialize (E (t, vs) Hin). cbv beta in E. cbn [fst snd] in E.
exact (rt_glob_of_b t _ rate_B_globs E).
Qed.
Lemma rate_B_u64_glob : forall t vs, In (t, vs) rate_B_u64 ->
  exists sz, In (t, sz) rate_B_globs /\ 8 * Z.of_nat (length vs) <= sz.
Proof.
intros t vs Hin. pose proof rate_B_marked_chk_ok as E. unfold rate_B_marked_chk in E.
apply andb_true_iff in E. destruct E as [_ E].
rewrite forallb_forall in E. specialize (E (t, vs) Hin). cbv beta in E. cbn [fst snd] in E.
exact (rt_glob_of_b t _ rate_B_globs E).
Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition rate_B_img_facts : Prop := rt_img_facts segs B rate_himg_B IMG_LO IMG_TOP.
(* The read ranges of image B's strings and tables hold no owned static and no errno byte. *)
Lemma rate_B_str_unowned : forall a s, rate_B_img_facts -> In (a, s) rate_B_strs ->
  rt_ro_unowned B a (Z.of_nat (length s) + 1).
Proof.
intros a s (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (a, Z.of_nat (length s) + 1)). unfold rt_ro_ranges. apply in_or_app. left.
exact (in_map (fun s0 : Z * list Z => (fst s0, Z.of_nat (length (snd s0)) + 1)) rate_B_strs (a, s) Hin).
Qed.
Lemma rate_B_i32_unowned : forall t vs, rate_B_img_facts -> In (t, vs) rate_B_i32 ->
  rt_ro_unowned B t (4 * Z.of_nat (length vs)).
Proof.
intros t vs (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (t, 4 * Z.of_nat (length vs))). unfold rt_ro_ranges. apply in_or_app. right. apply in_or_app. left.
exact (in_map (fun t0 : Z * list Z => (fst t0, 4 * Z.of_nat (length (snd t0)))) rate_B_i32 (t, vs) Hin).
Qed.
Lemma rate_B_u64_unowned : forall t vs, rate_B_img_facts -> In (t, vs) rate_B_u64 ->
  rt_ro_unowned B t (8 * Z.of_nat (length vs)).
Proof.
intros t vs (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (t, 8 * Z.of_nat (length vs))). unfold rt_ro_ranges. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. left.
exact (in_map (fun t0 : Z * list Z => (fst t0, 8 * Z.of_nat (length (snd t0)))) rate_B_u64 (t, vs) Hin).
Qed.
(* A string or table of image B's record, at an AR state whose bytes there are those of a state where it held,
   holds again (its shadow from rate_B_img_facts). *)
Lemma rate_B_cstr_at : forall a s ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_B_img_facts -> In (a, s) rate_B_strs -> AR segs B ly S W mem md -> rt_cstr segs H0 mem0 a s ->
  (forall i, 0 <= i <= Z.of_nat (length s) -> aview segs (w_H W) mem (a + i) = aview segs H0 mem0 (a + i)) ->
  rt_cstr segs (w_H W) mem a s.
Proof.
intros a s ly S W mem md H0 mem0 (_ & HG & HV) Hin HAR Hc Heq.
destruct (rate_B_str_glob a s Hin) as ((sz & Hg & Hsz) & Hlo & Hhi).
exact (rt_cstr_at segs B rate_B_globs IMG_LO IMG_TOP ly S W mem md H0 mem0 a s sz HG HV HAR Hg Hsz Hlo Hhi Hc Heq).
Qed.
Lemma rate_B_i32tab_at : forall t vs ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_B_img_facts -> In (t, vs) rate_B_i32 -> AR segs B ly S W mem md -> rt_i32tab segs H0 mem0 t vs ->
  (forall i, 0 <= i < 4 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
  rt_i32tab segs (w_H W) mem t vs.
Proof.
intros t vs ly S W mem md H0 mem0 (_ & HG & _) Hin HAR Hc Heq.
destruct (rate_B_i32_glob t vs Hin) as (sz & Hg & Hsz).
exact (rt_i32tab_at segs B rate_B_globs ly S W mem md H0 mem0 t vs sz HG HAR Hg Hsz Hc Heq).
Qed.
Lemma rate_B_u64tab_at : forall t vs ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_B_img_facts -> In (t, vs) rate_B_u64 -> AR segs B ly S W mem md -> rt_u64tab segs H0 mem0 t vs ->
  (forall i, 0 <= i < 8 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
  rt_u64tab segs (w_H W) mem t vs.
Proof.
intros t vs ly S W mem md H0 mem0 (_ & HG & _) Hin HAR Hc Heq.
destruct (rate_B_u64_glob t vs Hin) as (sz & Hg & Hsz).
exact (rt_u64tab_at segs B rate_B_globs ly S W mem md H0 mem0 t vs sz HG HAR Hg Hsz Hc Heq).
Qed.
End f.

Print Assumptions rate_B_site_malloc_pod.
Print Assumptions rate_B_site_malloc_buf.
Print Assumptions rate_B_site_cut3.
Print Assumptions rate_B_site_cut6.
Print Assumptions rate_B_str_glob.
Print Assumptions rate_B_i32_glob.
Print Assumptions rate_B_u64_glob.
Print Assumptions rate_B_str_unowned.
Print Assumptions rate_B_i32_unowned.
Print Assumptions rate_B_u64_unowned.
Print Assumptions rate_B_cstr_at.
Print Assumptions rate_B_i32tab_at.
Print Assumptions rate_B_u64tab_at.
