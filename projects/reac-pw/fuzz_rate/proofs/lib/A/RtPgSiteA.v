(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the call-site lemmas of rule 1j-bis for the
   texts of lib/A/RtPgCSpec.v, at the states those texts already state (the segment contracts' starts and ends, with
   image A's record RtPgImgA.rate_himg_A). Each lemma shows that the stated state supplies a premise of the next
   call's contract. Proves no function (kind: statement text).
   - rate_A_site_malloc_pod: at C2 (0x828b4, rate_build_contract's end) a0 = len + (len == 0) = len, and
     8 <= len <= 5440 < MALLOC_MAX: the request premise `0 <= n < MALLOC_MAX` of the allocator's contract
     (lib/Reusable/YG0d.v amalloc_realizes) and the pod size rate_check_contract reads.
   - rate_A_site_malloc_buf: at C5 (0x82e94) a0 = buflen + (buflen == 0) in [1, 23] < MALLOC_MAX, the request and
     the buf size rate_csv_contract reads.
   - rate_A_site_cut3 / rate_A_site_cut6: at C3 (0x828b8) and C6 (0x82e98) the start values of
     rate_check_contract / rate_csv_contract hold when the malloc call kept every location of the cut list but a0,
     which holds the block.
   - rate_A_site_strs: at a segment's start, the string, cell and table premises of the callee contracts the
     segments call (rt_check_code_specX at tbl = 0x9bc40 and lnone = 0x215c0; rt_refuse_code_specX at tbl = 0x9bc80
     and cov = 0x21600; rt_check_list_specX and rt_check_csv_specX at tcl = 0x21520; rt_drivable_csv_specX at
     afmt = 0x216c0, acomma = 0x216e0, aempty = 0x21700, tord = 0x216a0; rt_parse_specX at akey = 0x21720 and
     dcs = the three doubles; the harness's own strcmp key at 0x20fa0) follow from the start state's rt_seg_pre;
     its third conjunct, with rt_refuse_code_specX's post, is check_code's string premise: reac_rate_refuse_code's
     answer for r <= 4 is the address of the string whose text check_code asks for.
   - after a call that lets runtime-owned bytes change: rate_A_img_facts (RtPgCSpec.rt_img_facts at image A) and the
     lemmas that rebuild a string or table premise at the state after such a call from the one before it:
     rate_A_{str,i32,u64}_glob, rate_A_{str,i32,u64}_unowned, rate_A_cstr_at, rate_A_i32tab_at, rate_A_u64tab_at. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK04 YA0n YI04 YP09 YG0v YG00 YG0f YG0n YG0d YCbq YC5d YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Spa Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA.
Import ListNotations.
Local Open Scope Z_scope.

(* ===================== C2 and C5: the two malloc requests ===================== *)
(* check_csv's stack use in image A (`addi sp,sp,-160` 0x838e0, then `andi sp,sp,-32`, and the bcmp wrapper's
   2 ESTACK window): the T at which image A's walks instantiate RtPgCSpec.rt_check_csv_specX. Image B's frame is
   192 and its bound is stated in its own files. *)
Definition T_csv_STK : Z := 160 + 16 + 2 * ESTACK.

Lemma rate_A_site_malloc_pod : forall (e : rt_renv) (rest : list byte), q_len e = rt_len rest ->
rt_xv e XLenNZ = q_len e /\ 8 <= q_len e <= 5440 /\ 0 <= rt_xv e XLenNZ < MALLOC_MAX.
Proof.
intros e rest He. pose proof (rt_len_bounds rest) as Hb. rewrite <- He in Hb. cbn [rt_xv].
destruct (Z.eqb_spec (q_len e) 0) as [E0|E0]; [lia|].
unfold MALLOC_MAX. lia.
Qed.

Lemma rate_A_site_malloc_buf : forall (e : rt_renv), rt_hdr_ok e ->
rt_xv e XBl = rt_bl (q_buflen e) /\ 1 <= rt_bl (q_buflen e) <= 23 /\ 0 <= rt_xv e XBl < MALLOC_MAX.
Proof.
intros e He. destruct He as (_ & _ & Hb & _). cbn [rt_xv]. unfold rt_bl.
destruct (Z.eqb_spec (q_buflen e) 0) as [E0|E0]; unfold MALLOC_MAX; lia.
Qed.

(* ===================== C3 and C6: the values after a malloc returns ===================== *)
Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma rate_A_site_cut3 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rt_renv),
rt_cut segs H mem regs e (hi_L2 rate_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (q_pod e) ->
(forall r, In (LReg r) (map fst rate_A_L23_tl) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o, In (LCell b o) (map fst rate_A_L23_tl) -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (rt_xv e b + o + i) = mbyte segs (mrestrict H mem) (rt_xv e b + o + i)) ->
rt_cut segs H mem' regs' e (hi_L3 rate_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hr Hc.
unfold rt_cut in HC |- *.
change (hi_L2 rate_himg_A) with ((LReg 10, XLenNZ) :: rate_A_L23_tl) in HC.
change (hi_L3 rate_himg_A) with ((LReg 10, XPod) :: rate_A_L23_tl).
rewrite Forall_cons_iff in HC. destruct HC as [_ HC].
apply Forall_cons.
- cbn [fst snd rt_at rt_xv]. exact H10.
- exact (rt_cut_keep segs H mem mem' regs regs' e rate_A_L23_tl HC Hr Hc).
Qed.

Lemma rate_A_site_cut6 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rt_renv),
rt_cut segs H mem regs e (hi_L5 rate_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (q_buf e) ->
(forall r, In (LReg r) (map fst rate_A_L56_tl) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o, In (LCell b o) (map fst rate_A_L56_tl) -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (rt_xv e b + o + i) = mbyte segs (mrestrict H mem) (rt_xv e b + o + i)) ->
rt_cut segs H mem' regs' e (hi_L6 rate_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hr Hc.
unfold rt_cut in HC |- *.
change (hi_L5 rate_himg_A) with ((LReg 10, XBl) :: rate_A_L56_tl) in HC.
change (hi_L6 rate_himg_A) with ((LReg 10, XBuf) :: rate_A_L56_tl).
rewrite Forall_cons_iff in HC. destruct HC as [_ HC].
apply Forall_cons.
- cbn [fst snd rt_at rt_xv]. exact H10.
- exact (rt_cut_keep segs H mem mem' regs regs' e rate_A_L56_tl HC Hr Hc).
Qed.
End c3.

(* ============ the callees' strings, cells and tables at a segment's start ============ *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rate_A_site_strs : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc RLO RHI e pos,
rt_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc rate_himg_A RLO RHI e pos ->
(forall i, 0 <= i < 4 ->
 rt_cstr segs (w_H W) memc (nth (Z.to_nat i) [0x21540; 0x21560; 0x21580; 0x215a0] 0) (rt_code_of_txt (i + 1))) /\
rt_cstr segs (w_H W) memc 0x215c0 (rt_code_of_txt 0) /\
(forall r, 0 <= r <= 4 ->
 rt_cstr segs (w_H W) memc (rt_refuse [0x21600; 0x21620; 0x21640; 0x21660; 0x21680] 0x21600 r) (rt_refuse_txt r)) /\
rt_cstr segs (w_H W) memc 0x21720 (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
rt_cstr segs (w_H W) memc 0x20fa0 (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
rt_cstr segs (w_H W) memc 0x216c0 STR_FMT_SD /\
rt_cstr segs (w_H W) memc 0x216e0 STR_COMMA /\
rt_cstr segs (w_H W) memc 0x21700 STR_EMPTY /\
rt_ro_cells segs (w_H W) memc
  [(0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10338, 0x41e0000000000000)] /\
rt_i32tab segs (w_H W) memc 0x21520 RateCfg.closed_list /\
rt_i32tab segs (w_H W) memc 0x216a0 RateCfg.closed_list /\
rt_u64tab segs (w_H W) memc 0x9bc40 [0x21540; 0x21560; 0x21580; 0x215a0] /\
rt_u64tab segs (w_H W) memc 0x9bc80 [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & HC & _ & _ & HI & HU).
cbn [hi_strs hi_cells hi_i32 hi_u64 rate_himg_A] in HS, HC, HI, HU.
assert (Hs : forall a s, In (a, s) rate_A_strs -> rt_cstr segs (w_H W) memc a s)
  by (intros a s Hin; exact (proj1 (Forall_forall _ _) HS (a, s) Hin)).
assert (Hc : forall a v, In (a, v) rate_A_cells -> val_mem segs (mrestrict (w_H W) memc) a 8 v)
  by (intros a v Hin; exact (proj1 (Forall_forall _ _) HC (a, v) Hin)).
assert (Hi : forall t vs, In (t, vs) rate_A_i32 -> rt_i32tab segs (w_H W) memc t vs)
  by (intros t vs Hin; exact (proj1 (Forall_forall _ _) HI (t, vs) Hin)).
assert (Hu : forall t vs, In (t, vs) rate_A_u64 -> rt_u64tab segs (w_H W) memc t vs)
  by (intros t vs Hin; exact (proj1 (Forall_forall _ _) HU (t, vs) Hin)).
split.
{ intros i Hi4. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  destruct C as [->|[->|[->| ->]]]; cbn [Z.to_nat nth];
    apply Hs; unfold rate_A_strs; cbn [In]; repeat (first [left; reflexivity | right]). }
split; [apply Hs; unfold rate_A_strs; cbn [In]; repeat (first [left; reflexivity | right])|].
split.
{ intros r Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as C by lia.
  destruct C as [->|[->|[->|[->| ->]]]]; unfold rt_refuse; cbn [Z.leb Z.to_nat nth];
    apply Hs; unfold rate_A_strs; cbn [In]; repeat (first [left; reflexivity | right]). }
repeat (split; [solve [ apply Hs; unfold rate_A_strs; cbn [In]; repeat (first [left; reflexivity | right])
                      | unfold rt_ro_cells; repeat constructor; cbn [fst snd]; apply Hc; unfold rate_A_cells;
                        cbn [In]; repeat (first [left; reflexivity | right])
                      | apply Hi; unfold rate_A_i32; cbn [In]; repeat (first [left; reflexivity | right])
                      | apply Hu; unfold rate_A_u64; cbn [In]; repeat (first [left; reflexivity | right]) ] |]).
apply Hu; unfold rate_A_u64; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.
End s.

(* ============ after a call that lets runtime-owned bytes change: image A's read-only facts ============
   RtPgCSpec.rt_img_facts at image A's record and range [IMG_LO, IMG_TOP) = [0x10000, 0x5fa000)
   (lib/Reusable/YImgTop.v): the hypothesis image A's walks take, with AR_laws, to re-derive a string, table or cell
   fact after a malloc, a side-stack frame or an rt_cpost_o call (reac_rate_drivable_csv's format, separators and
   ordered after its class-1 frame; check_csv's closed_list after its class-2 frame; the main walk's after
   reac_rate_drivable_csv returns and after each malloc). Image A's close proves it at its symbol record. Below: each
   string and table of the record is a registered global of hi_globs with room for it (each string also 64 bytes
   inside the range, for its shadow hull; the tables' predicates read no hull), and its bytes are no owned static, so
   RtPgBase.rt_img_unowned and rt_cstr_at / rt_i32tab_at / rt_u64tab_at apply. *)
Definition rate_A_marked_chk : bool :=
  forallb (fun s => existsb (fun g => (fst g =? fst s) && (Z.of_nat (length (snd s)) + 1 <=? snd g)) rate_A_globs &&
                    (IMG_LO + 64 <=? fst s) && (fst s + Z.of_nat (length (snd s)) + 1 + 64 <=? IMG_TOP)) rate_A_strs &&
  forallb (fun t => existsb (fun g => (fst g =? fst t) && (4 * Z.of_nat (length (snd t)) <=? snd g)) rate_A_globs)
    rate_A_i32 &&
  forallb (fun t => existsb (fun g => (fst g =? fst t) && (8 * Z.of_nat (length (snd t)) <=? snd g)) rate_A_globs)
    rate_A_u64.
Lemma rate_A_marked_chk_ok : rate_A_marked_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_A_str_glob : forall a s, In (a, s) rate_A_strs ->
  (exists sz, In (a, sz) rate_A_globs /\ Z.of_nat (length s) + 1 <= sz) /\
  IMG_LO + 64 <= a /\ a + Z.of_nat (length s) + 1 + 64 <= IMG_TOP.
Proof.
intros a s Hin. pose proof rate_A_marked_chk_ok as E. unfold rate_A_marked_chk in E.
apply andb_true_iff in E. destruct E as [E _]. apply andb_true_iff in E. destruct E as [E _].
rewrite forallb_forall in E. specialize (E (a, s) Hin). cbv beta in E. cbn [fst snd] in E.
apply andb_true_iff in E. destruct E as [E Hhi]. apply andb_true_iff in E. destruct E as [Ex Hlo].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
split; [exact (rt_glob_of_b a _ rate_A_globs Ex)|]. split; [exact Hlo | exact Hhi].
Qed.
Lemma rate_A_i32_glob : forall t vs, In (t, vs) rate_A_i32 ->
  exists sz, In (t, sz) rate_A_globs /\ 4 * Z.of_nat (length vs) <= sz.
Proof.
intros t vs Hin. pose proof rate_A_marked_chk_ok as E. unfold rate_A_marked_chk in E.
apply andb_true_iff in E. destruct E as [E _]. apply andb_true_iff in E. destruct E as [_ E].
rewrite forallb_forall in E. specialize (E (t, vs) Hin). cbv beta in E. cbn [fst snd] in E.
exact (rt_glob_of_b t _ rate_A_globs E).
Qed.
Lemma rate_A_u64_glob : forall t vs, In (t, vs) rate_A_u64 ->
  exists sz, In (t, sz) rate_A_globs /\ 8 * Z.of_nat (length vs) <= sz.
Proof.
intros t vs Hin. pose proof rate_A_marked_chk_ok as E. unfold rate_A_marked_chk in E.
apply andb_true_iff in E. destruct E as [_ E].
rewrite forallb_forall in E. specialize (E (t, vs) Hin). cbv beta in E. cbn [fst snd] in E.
exact (rt_glob_of_b t _ rate_A_globs E).
Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition rate_A_img_facts : Prop := rt_img_facts segs B rate_himg_A IMG_LO IMG_TOP.
(* The read ranges of image A's strings and tables hold no owned static and no errno byte. *)
Lemma rate_A_str_unowned : forall a s, rate_A_img_facts -> In (a, s) rate_A_strs ->
  rt_ro_unowned B a (Z.of_nat (length s) + 1).
Proof.
intros a s (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (a, Z.of_nat (length s) + 1)). unfold rt_ro_ranges. apply in_or_app. left.
exact (in_map (fun s0 : Z * list Z => (fst s0, Z.of_nat (length (snd s0)) + 1)) rate_A_strs (a, s) Hin).
Qed.
Lemma rate_A_i32_unowned : forall t vs, rate_A_img_facts -> In (t, vs) rate_A_i32 ->
  rt_ro_unowned B t (4 * Z.of_nat (length vs)).
Proof.
intros t vs (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (t, 4 * Z.of_nat (length vs))). unfold rt_ro_ranges. apply in_or_app. right. apply in_or_app. left.
exact (in_map (fun t0 : Z * list Z => (fst t0, 4 * Z.of_nat (length (snd t0)))) rate_A_i32 (t, vs) Hin).
Qed.
Lemma rate_A_u64_unowned : forall t vs, rate_A_img_facts -> In (t, vs) rate_A_u64 ->
  rt_ro_unowned B t (8 * Z.of_nat (length vs)).
Proof.
intros t vs (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (t, 8 * Z.of_nat (length vs))). unfold rt_ro_ranges. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. left.
exact (in_map (fun t0 : Z * list Z => (fst t0, 8 * Z.of_nat (length (snd t0)))) rate_A_u64 (t, vs) Hin).
Qed.
(* A string or table of image A's record, at an AR state whose bytes there are those of a state where it held,
   holds again (its shadow from rate_A_img_facts). *)
Lemma rate_A_cstr_at : forall a s ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_A_img_facts -> In (a, s) rate_A_strs -> AR segs B ly S W mem md -> rt_cstr segs H0 mem0 a s ->
  (forall i, 0 <= i <= Z.of_nat (length s) -> aview segs (w_H W) mem (a + i) = aview segs H0 mem0 (a + i)) ->
  rt_cstr segs (w_H W) mem a s.
Proof.
intros a s ly S W mem md H0 mem0 (_ & HG & HV) Hin HAR Hc Heq.
destruct (rate_A_str_glob a s Hin) as ((sz & Hg & Hsz) & Hlo & Hhi).
exact (rt_cstr_at segs B rate_A_globs IMG_LO IMG_TOP ly S W mem md H0 mem0 a s sz HG HV HAR Hg Hsz Hlo Hhi Hc Heq).
Qed.
Lemma rate_A_i32tab_at : forall t vs ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_A_img_facts -> In (t, vs) rate_A_i32 -> AR segs B ly S W mem md -> rt_i32tab segs H0 mem0 t vs ->
  (forall i, 0 <= i < 4 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
  rt_i32tab segs (w_H W) mem t vs.
Proof.
intros t vs ly S W mem md H0 mem0 (_ & HG & _) Hin HAR Hc Heq.
destruct (rate_A_i32_glob t vs Hin) as (sz & Hg & Hsz).
exact (rt_i32tab_at segs B rate_A_globs ly S W mem md H0 mem0 t vs sz HG HAR Hg Hsz Hc Heq).
Qed.
Lemma rate_A_u64tab_at : forall t vs ly S (W : world segs) mem md (H0 : word -> bool) mem0,
  rate_A_img_facts -> In (t, vs) rate_A_u64 -> AR segs B ly S W mem md -> rt_u64tab segs H0 mem0 t vs ->
  (forall i, 0 <= i < 8 * Z.of_nat (length vs) -> aview segs (w_H W) mem (t + i) = aview segs H0 mem0 (t + i)) ->
  rt_u64tab segs (w_H W) mem t vs.
Proof.
intros t vs ly S W mem md H0 mem0 (_ & HG & _) Hin HAR Hc Heq.
destruct (rate_A_u64_glob t vs Hin) as (sz & Hg & Hsz).
exact (rt_u64tab_at segs B rate_A_globs ly S W mem md H0 mem0 t vs sz HG HAR Hg Hsz Hc Heq).
Qed.
End f.

Print Assumptions rate_A_site_malloc_pod.
Print Assumptions rate_A_site_malloc_buf.
Print Assumptions rate_A_site_cut3.
Print Assumptions rate_A_site_cut6.
Print Assumptions rate_A_site_strs.
Print Assumptions rate_A_str_glob.
Print Assumptions rate_A_i32_glob.
Print Assumptions rate_A_u64_glob.
Print Assumptions rate_A_str_unowned.
Print Assumptions rate_A_i32_unowned.
Print Assumptions rate_A_u64_unowned.
Print Assumptions rate_A_cstr_at.
Print Assumptions rate_A_i32tab_at.
Print Assumptions rate_A_u64tab_at.
