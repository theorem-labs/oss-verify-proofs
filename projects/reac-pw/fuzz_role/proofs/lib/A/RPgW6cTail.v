(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the two calls that end
   ent_build's cases 6, 7 and 8 (pod.h:347, 356, 364) and the jump to the join J 0x8165c. Proves no function (kind:
   segment lemma): the callees are the Section hypotheses AMEMCPY / AMEMSET, the kernel's YG0d.aintrin_realizes at
   __asan_memcpy 0x510d4 and __asan_memset 0x51570.

   THE CODE (listing of image A).
     cases 6, 7:  0x81514 s9 := s8 + a2; a1 -= a2; sd a1,0xf8(s1); ld a0,0xc0(s1) (= F + 0xf8); mv a1,s8;
                  0x81528 jal __asan_memcpy (e.body, the input at the cursor, n);  0x8152c j 0x8165c
     case 8:      0x81430 sw a2,4(a0) (e.size); mv a0,a3 (= F + 0xf8); a1 := 0; 0x81440 jal __asan_memset;
                  0x81444 sd s4,0xf8(s1); mv s9,s8; ld s4,0xb0(s1); j 0x8165c
   The case heads (lib/A/RPgW6c6.v, RPgW6c7.v, RPgW6c8.v) run up to the callee's entry; this file takes the call and
   the rest. The post w6c_jpost is the join's state in the shape the glue (lib/A/RPgW6c.v) turns into RPgSeg's
   rs_cut_J: the journal (no event), the I/O state, the registers the cut keeps, s4 and s9, every byte outside the
   callee's stack [R - ESTACK, R), e (F + 0xf0, 104 bytes) and the cell R + 0xf8 kept, e's bytes and R + 0xf8's
   value. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition W6C_J : Z := 0x8165c.
Definition W6C_CPY : Z := 0x510d4.
Definition W6C_SET : Z := 0x51570.
Definition W6C_RCPY : Z := 0x8152c.
Definition W6C_RSET : Z := 0x81444.

(* the code words the three cases and their tails run through, with the slow blocks of their checks *)
Definition w6c_tbl : ctable :=
  build_table rsegs 0x80f64 29 (build_table rsegs 0x810a8 55 (build_table rsegs 0x811c0 2
  (build_table rsegs 0x81254 4 (build_table rsegs 0x81354 5 (build_table rsegs 0x81418 70
  (build_table rsegs 0x819bc 50 TEmpty)))))).
Lemma w6c_tbl_ok : table_ok rsegs w6c_tbl.
Proof.
unfold w6c_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
Lemma w6c_wx : wx_segs_nowrap rsegs.
Proof. exact RPgCfgChanges.cfg_wx. Qed.
Lemma w6c_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact RPgCfgChanges.cfg_segs_low. Qed.
Lemma w6c_ret_cpy : YK0s.ret_ok (Z_to_bv 64 W6C_RCPY).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w6c_ret_set : YK0s.ret_ok (Z_to_bv 64 W6C_RSET).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* the registers rs_cut_J keeps from the case entry (RPgSeg rs_Rc: s0 s1 s2 s3 s5 s6 s7 s10 s11) and sp, gp, tp *)
Definition w6c_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 26; 27]%bv.
Lemma w6c_keep_saved : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
forall r, In r w6c_keep -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
cbv [w6c_keep In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<-|Hr];
  [match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia|]).
destruct Hr.
Qed.

(* e's bytes after the two header stores and a copy of bs into the body, and after a fill of zeros *)
Lemma w6c_skipn_repeat : forall {A} (x : A) n m, skipn n (repeat x m) = repeat x (m - n).
Proof. intros A x n. induction n as [|n IH]; intros [|m]; cbn; try reflexivity. apply IH. Qed.
Lemma w6c_ent_cpy : forall ty sz (bs : list byte), (length bs <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
Model.overwrite (le32 ty ++ le32 sz ++ zeros 96) 8 bs = ent_mem (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))).
Proof.
intros ty sz bs H1 H2.
assert (L8 : length (le32 ty ++ le32 sz) = 8%nat) by (rewrite length_app, !length_le32; reflexivity).
unfold Model.overwrite. rewrite (app_assoc (le32 ty) (le32 sz) (zeros 96)).
rewrite firstn_app, L8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
rewrite skipn_app, L8. rewrite (skipn_all2 (le32 ty ++ le32 sz)) by lia. cbn [app].
replace (8 + length bs - 8)%nat with (length bs) by lia.
unfold zeros. rewrite w6c_skipn_repeat.
unfold ent_mem. cbn [e_type e_size e_body]. rewrite <- app_assoc. do 2 f_equal.
rewrite length_app, repeat_length, <- app_assoc, <- repeat_app. do 2 f_equal. lia.
Qed.
Lemma w6c_ent_set : forall ty sz, (Z.to_nat sz <= 96)%nat ->
le32 ty ++ le32 sz ++ zeros 96 = ent_mem (Ent ty sz (zeros (Z.to_nat sz))).
Proof.
intros ty sz H. unfold ent_mem. cbn [e_type e_size e_body]. do 2 f_equal.
rewrite length_zeros. unfold zeros. rewrite <- repeat_app. f_equal. lia.
Qed.

(* a value read back out of a region's CVal chunk, and a region of the final state *)
Lemma w6c_region_nth : forall {fx : YK11.FPState} E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros fx E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w6c_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* the real frame R and the frame for locals F at a case entry (RPgSeg rs_pre: R 16-aligned with the real frame
   below the entry sp and the callees' stack inside the journal's window; F the side-stack frame (3, pos)) *)
Definition w6c_geo (STK sp0 : Z) (own : list (Z * Z)) (lyc : alayout) (R F pos : Z) : Prop :=
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R + 0x1a0 <= sp0 /\ kHighMemBeg <= R - T_SEG_STK /\
In (3, pos) own /\ F = frame_addr lyc 3 pos /\ in_app F 512 /\ F mod 32 = 0.

(* the join's state *)
Definition w6c_jpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
(R F : Z) (ed : ent) (cur' nl' sa : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
W2 = W /\ c2 = cfg_at rsegs W6C_J regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r w6c_keep -> getr regs2 r = getr regs r) /\
getr regs2 20 = w64 sa /\ getr regs2 25 = w64 cur' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) -> ~ (R + 0xf8 <= a < R + 0x100) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
rm_bytes rsegs (w_H W) mem2 (F + 0xf0) (ent_mem ed) /\
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 (nl' mod 2 ^ 64).

(* a block before the call: what it changed is inside the join's write set *)
Lemma w6c_jpost_trans : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mem1 md1 regs1
R F ed cur' nl' sa W2 c2,
(forall r, In r w6c_keep -> getr regs1 r = getr regs r) -> same_io mdc md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) -> ~ (R + 0xf8 <= a < R + 0x100) ->
 aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem1 md1 regs1 R F ed cur' nl' sa W2 c2 ->
w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mem1 md1 regs1 R F ed cur' nl' sa W2 c2
Hk1 Hio1 Hm1 (regs2 & mem2 & md2 & HW & Hc & HJ & Hio & Hk & H20 & H25 & Hm & He & Hs).
exists regs2, mem2, md2. split; [exact HW|]. split; [exact Hc|]. split; [exact HJ|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio]|].
split; [intros r Hr; rewrite (Hk r Hr); exact (Hk1 r Hr)|].
split; [exact H20|]. split; [exact H25|]. split; [|split; [exact He | exact Hs]].
intros a Ha H1 H2 H3. rewrite (Hm a Ha H1 H2 H3). exact (Hm1 a Ha H1 H2 H3).
Qed.

(* aj_intrin_at (lib/Reusable/YCbq.v) with the callee's same_but_materialized kept as same_io *)
Lemma w6c_intrin_at : forall op pc, aintrin_realizes rsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
match op with OCpy => aview rsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS w6c_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; unfold ESTACK in *; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized mdc md2 Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.

(* the frame's facts every tail uses *)
Lemma w6c_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> w6c_geo STK sp0 own lyc R F pos ->
F + 512 <= alloc_ceiling /\ 4096 <= F /\ F + 512 <= 2 ^ 47 /\ alloc_ceiling <= R - T_SEG_STK /\ sp0 mod 16 = 0 /\ sp0 <= 2 ^ 47 /\
(forall i, 0 <= i < 64 -> aview rsegs (w_H W) memc (shadow_addr F + i) <> None) /\
(forall a, F <= a < F + 512 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & _ & HFS).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HFS. rewrite <- HF in HF4096, HFceil, HFS.
pose proof alloc_ceiling_lt as Hc47.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|].
split; [intros i Hi; apply (aview_some_of_apresent rsegs); exact (proj1 (HFS i Hi))|].
intros a Ha. right; right; right. exists 3, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
rewrite <- HF. change (fs_frame_bytes 3) with 512. lia.
Qed.

(* the shadow hull of [F + o, F + o + n) inside e lies in the frame's 64 shadow bytes *)
Lemma w6c_hull_e : forall (rd : reader) F o n, F mod 32 = 0 -> 0 <= F -> 0xf0 <= o -> o + n <= 0x158 -> 0 < n ->
(forall i, 0 <= i < 64 -> rd (shadow_addr F + i) <> None) -> shadow_hull_vis rd (F + o) n.
Proof.
intros rd F o n HF H0 Ho Hn Hn0 Hsh s Hs.
assert (E1 : forall c, 0 <= c -> shadow_addr (F + c) = shadow_addr F + c / 8).
{ intros c Hc. unfold shadow_addr.
  destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
  replace (q * 32 + c) with (c + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
  replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by lia.
rewrite (E1 o) in Hs by lia. rewrite (E1 (o + n - 1)) in Hs by lia.
set (X := shadow_addr F) in *.
assert (A1 : 30 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (A2 : (o + n - 1) / 8 < 43) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (X + o / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + o / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (X + (o + n - 1) / 8) 8 ltac:(lia)).
replace s with (X + (s - X)) by lia. apply Hsh. lia.
Qed.

Lemma w6c_val_kept : forall H m H' m' a n v, val_mem rsegs (mrestrict H m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H m H' m' a n v V K k Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat k)) by (apply K; lia).
exact (V k Hk).
Qed.
Lemma w6c_frame_nil : forall E (H : word -> bool) m m', frame_of E [] m m' -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. apply (aview_eq_of rsegs). unfold mrestrict. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & _). destruct Hin.
Qed.
Lemma rs_PJ_sh : rs_PJ = rm_sh false false false true false.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F HF. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.

(* the join from the engine's last state *)
Lemma w6c_leaf : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa E ss ms md,
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = W6C_J ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
(forall r, In r w6c_keep -> getr (ms_regs ms) r = getr regs r) ->
getr (ms_regs ms) 20 = w64 sa -> getr (ms_regs ms) 25 = w64 cur' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) -> ~ (R + 0xf8 <= a < R + 0x100) ->
 aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0xf0) (ent_mem ed) ->
val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xf8) 8 (nl' mod 2 ^ 64) ->
SRr rsegs W (mkCfg ms md) (w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa E ss ms md
HS Hrv Hpc HJ Hio Hk H20 H25 Hm He Hs.
apply SRr_ret. exists (ms_regs ms), (ms_mem ms), md. split; [reflexivity|].
split; [unfold cfg_at, w64; rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
repeat (split; [eassumption|]). exact Hs.
Qed.

(* ===================== cases 6 and 7: memcpy(e.body, src, n), then `j J` ===================== *)
Lemma w6c_tail_cpy : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz src
(bs : list byte) cur' nl' sa,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6c_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6C_RCPY -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (F + 0xf8) -> getr regs 11 = w64 src -> getr regs 12 = w64 (Z.of_nat (length bs)) ->
getr regs 20 = w64 sa -> getr regs 25 = w64 cur' ->
(length bs <= Z.to_nat sz)%nat -> 0 <= sz <= 96 ->
rm_bytes rsegs (w_H W) memc (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96) ->
rm_bytes rsegs (w_H W) memc src bs ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF src (Z.of_nat (length bs)) ->
(0 < Z.of_nat (length bs) -> shadow_hull_vis (aview rsegs (w_H W) memc) src (Z.of_nat (length bs))) ->
amem_range src (Z.of_nat (length bs)) -> 0 <= src -> src + Z.of_nat (length bs) <= 2 ^ 63 ->
(forall a, src <= a < src + Z.of_nat (length bs) -> ~ (R - ESTACK <= a < R) /\ ~ (F + 0xf0 <= a < F + 0x158)) ->
rl_fsh rsegs (w_H W) memc F rs_PJ ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (nl' mod 2 ^ 64) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6C_CPY) memc (seg_rom rsegs)) mdc)
(w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))) cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz src bs cur' nl' sa
HJ HG H1 H2 H3 H4 H10 H11 H12 H20 H25 Hlen Hsz He Hbs Hra Hhl Hamr Hsrc0 Hsrc63 Hdis Hfsh Hslot.
destruct (w6c_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
set (n := Z.of_nat (length bs)) in *.
assert (Hn96 : 0 <= n <= 96) by (subst n; lia).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (HspR : spZ regs = R).
{ unfold spZ. rewrite H2. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
eapply SRr_bind.
{ apply (w6c_intrin_at OCpy W6C_CPY AMEMCPY W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (F + 0xf8)
    src n (R - sp0) (w64 W6C_RCPY) HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact w6c_ret_cpy.
  - intros a Ha. split; [apply HFw; lia|]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - unfold in_app, ASAN_CEIL in HFapp. unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - replace (F + 0xf8) with (F + RM_E + 8) by (unfold RM_E; lia).
    apply (rm_A_ra_e rsegs _ _ F false false false false 8 n); [rewrite <- rs_PJ_sh; exact Hfsh | apply w6c_F8; exact HF32 | lia | lia].
  - intros Hn0. apply w6c_hull_e; [exact HF32 | lia | lia | lia | lia | exact HFS].
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite HspR; exact (proj1 (Hdis a Ha))].
      pose proof (proj1 (rm_bytes_aview rsegs _ _ _ _) Hbs (Z.to_nat (a - src)) ltac:(subst n; lia)) as Hv.
      rewrite Z2Nat.id in Hv by lia. replace (src + (a - src)) with a in Hv by lia. rewrite Hv. discriminate. }
    split.
    { destruct (Z_le_gt_dec (F + 0xf8 + n) src) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (src + n) (F + 0xf8)) as [Y|Y]; [right; exact Y|].
      exfalso. apply (proj2 (Hdis (Z.max src (F + 0xf8)) ltac:(lia))). lia. }
    split; [exact Hamr|]. split; [exact Hra | exact Hhl]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & Ha02 & Heff & Hfr & Hpres).
(* the jump at 0x8152c *)
assert (HS : st_ok rsegs (Ereg regs2 []) (mkSS W6C_RCPY sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 W6C_RCPY) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof LAWS as HL.
change (w64 W6C_RCPY) with (Z_to_bv 64 W6C_RCPY).
aj_run_to w6c_tbl_ok HS HJ2 W6C_J.
{ apply awr_ok_nil. }
(* at J *)
assert (HE3 : forall a, aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ lazymatch goal with Hx : frame_of ?E ?rs mem2 (ms_mem ms) |- _ =>
    let rs' := eval vm_compute in rs in change (frame_of E rs' mem2 (ms_mem ms)) in Hx;
    intros a; exact (w6c_frame_nil _ (w_H W) _ _ Hx a) end. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. rewrite HE3. apply Hfr; [exact Ha | lia | lia]. }
eapply (w6c_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F _ cur' nl' sa _ _ _ _ HS).
- reflexivity.
- vm_compute. reflexivity.
- exact HJ2.
- eapply same_io_trans; [exact Hio2 | apply RPgCfgChanges.same_io_wvb].
- intros r Hr. rewrite (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W) [] HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) r).
  + exact (w6c_keep_saved regs regs2 HP2 r Hr).
  + cbv [w6c_keep In] in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; discriminate|]). destruct Hr.
  + intros [].
- rewrite (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W) [] HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) 20%bv
    ltac:(vm_compute; discriminate) (fun X => X)).
  exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) H20).
- rewrite (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W) [] HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) 25%bv
    ltac:(vm_compute; discriminate) (fun X => X)).
  exact (eq_trans (HP2 25 ltac:(unfold acallee_saved; lia)) H25).
- intros a Ha H5 H6 H7. exact (HM a Ha H5 H6).
- rewrite <- (w6c_ent_cpy ty sz bs) by lia.
  apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms)); [|intros x _; apply HE3].
  replace (F + 0xf8) with (F + 0xf0 + Z.of_nat 8) in Heff, Hfr by lia.
  apply (rm_bytes_patch rsegs (w_H W) memc (w_H W) mem2 (F + 0xf0) _ 8 bs He).
  + apply (rm_memcpy_bytes rsegs (w_H W) memc (w_H W) mem2 src (F + 0xf0 + Z.of_nat 8) bs Hbs).
    intros i Hi. exact (Heff i Hi).
  + rewrite !length_app, !length_le32, length_zeros. lia.
  + intros y Hy Hny. rewrite !length_app, !length_le32, length_zeros in Hy. rewrite Nat2Z.inj_add in Hny.
    unfold n in *. apply Hfr; [lia | lia |]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
- apply (w6c_val_kept (w_H W) memc (w_H W) (ms_mem ms)); [exact Hslot|].
  intros i Hi. unfold ESTACK, T_SEG_STK, ASTACK, kHighMemBeg in *. apply HM; [lia | lia | lia].
Qed.

(* ===================== case 8: memset(e.body, 0, size), then the four instructions to J ===================== *)
Definition w6c_RSs : YP09.region := YP09.mkRegion (Some 9%nat) 0xb0 0x100 0xf8 0x100 [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))].
Lemma w6c_kept_RSs : forall E (H : word -> bool) m m' R, bv_unsigned (ew E 9) = R -> frame_of E [w6c_RSs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' R H9 HF a Ha Hn. apply (aview_eq_of rsegs). unfold mrestrict. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & [<-|[]] & Hr). cbn [w6c_RSs YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite H9 in Hr.
rewrite unsigned_lit_small in Hr by lia. lia.
Qed.
Lemma w6c_ow_zeros : forall ty sz, (Z.to_nat sz <= 96)%nat ->
Model.overwrite (le32 ty ++ le32 sz ++ zeros 96) 8 (zeros (Z.to_nat sz)) = le32 ty ++ le32 sz ++ zeros 96.
Proof.
intros ty sz H. rewrite w6c_ent_cpy by (rewrite ?length_zeros; lia).
rewrite length_zeros, Nat.sub_diag. change (zeros 0) with (@nil byte). rewrite app_nil_r.
symmetry. apply w6c_ent_set. exact H.
Qed.
Lemma w6c_tail_set : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz cur' nl' sa,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6c_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6C_RSET -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 10 = w64 (F + 0xf8) -> getr regs 11 = w64 0 -> getr regs 12 = w64 sz ->
getr regs 20 = w64 nl' -> getr regs 24 = w64 cur' ->
0 <= sz <= 96 -> 0 <= sa < 2 ^ 64 ->
rm_bytes rsegs (w_H W) memc (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96) ->
rl_fsh rsegs (w_H W) memc F rs_PJ ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 sa ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6C_SET) memc (seg_rom rsegs)) mdc)
(w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F (Ent ty sz (zeros (Z.to_nat sz))) cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos ty sz cur' nl' sa
HJ HG H1 H2 H3 H4 H9 H10 H11 H12 H20 H24 Hsz Hsa He Hfsh Hsb.
destruct (w6c_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HF & HFapp & HF32).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk, HSTK, HRc.
assert (HspR : spZ regs = R).
{ unfold spZ. rewrite H2. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
eapply SRr_bind.
{ apply (w6c_intrin_at OSet W6C_SET AMEMSET W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (F + 0xf8)
    0 sz (R - sp0) (w64 W6C_RSET) HJ H10 H11 H12).
  - lia.
  - lia.
  - lia.
  - rewrite HspR. lia.
  - rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - exact w6c_ret_set.
  - intros a Ha. split; [apply HFw; lia|]. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - unfold in_app, ASAN_CEIL in HFapp. unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - replace (F + 0xf8) with (F + RM_E + 8) by (unfold RM_E; lia).
    apply (rm_A_ra_e rsegs _ _ F false false false false 8 sz); [rewrite <- rs_PJ_sh; exact Hfsh | apply w6c_F8; exact HF32 | lia | lia].
  - intros Hn0. apply w6c_hull_e; [exact HF32 | lia | lia | lia | lia | exact HFS].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & Ha02 & Heff & Hfr & Hpres).
assert (HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf8 <= a < F + 0xf8 + sz) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6. apply Hfr; [exact Ha | exact H5 | lia]. }
(* 0x81444 sd s4,0xf8(s1); mv s9,s8; ld s4,0xb0(s1); j J *)
assert (U9 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 sa]) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl).
  assert (E9 : getr regs2 9 = w64 R) by exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) H9).
  rewrite E9. unfold w64. apply unsigned_lit_small.
  unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 sa]) 32 = Z_to_bv 64 sa) by exact (ew_Ereg_extra regs2 [Z_to_bv 64 sa] 0).
assert (HS : st_ok rsegs (Ereg regs2 [Z_to_bv 64 sa]) (mkSS W6C_RSET sr_atoms [w6c_RSs] None
  (mkFacts [(9%nat, mkAF 0x10007fff8000 (2 ^ 47) 4)] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 W6C_RSET) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold w6c_RSs. apply (rm_rw_region rsegs _ (w_H W) mem2 9%nat R); [exact U9 | lia | lia | |].
    + intros o Ho. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply Hpres2. unfold T_SEG_STK, ASTACK in *. lia.
    + constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0xb0 8 (SOff 32 0) sa); [| cbn; lia | cbn; lia |].
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * apply (w6c_val_kept (w_H W) memc (w_H W) mem2); [exact Hsb|].
        intros i Hi. apply HK2; [lia | lia | unfold ESTACK in *; lia].
  - split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    split; [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia|]. split; [|lia].
    destruct (proj1 (Z.mod_divide R 16 ltac:(lia)) HR16) as [q ->]. change (2 ^ 4) with 16. apply Z_mod_mult. }
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof LAWS as HL.
change (w64 W6C_RSET) with (Z_to_bv 64 W6C_RSET).
aj_run_to w6c_tbl_ok HS HJ2 W6C_J.
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := R - sp0);
  [reflexivity | rewrite U9; lia | unfold w6c_RSs; cbn [YP09.r_wlo]; unfold T_SEG_STK, ASTACK in *; lia
  | unfold w6c_RSs; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* at J *)
assert (HE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a).
{ lazymatch goal with Hx : frame_of ?E ?rs mem2 (ms_mem ms) |- _ =>
    change (frame_of E [w6c_RSs] mem2 (ms_mem ms)) in Hx;
    intros a Ha Hn; exact (w6c_kept_RSs _ (w_H W) _ _ R U9 Hx a Ha Hn) end. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
  ~ (R + 0xf8 <= a < R + 0x100) -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha H5 H6 H7. rewrite (HE3 a Ha H7). apply HK2; [exact Ha | lia | exact H5]. }
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (20%bv) HS) as R20.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ ms (25%bv) HS) as R25.
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e20 := eval vm_compute in (sr_get (ss_regs ssf) (20%bv : bv 5)) in
  let e25 := eval vm_compute in (sr_get (ss_regs ssf) (25%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (20%bv : bv 5)) with e20 in R20;
  change (sr_get (ss_regs ssf) (25%bv : bv 5)) with e25 in R25;
  let r0 := eval vm_compute in (nth_error (ss_mem ssf) 0) in
  lazymatch r0 with Some ?rg =>
    assert (HR0 : region_ok rsegs (Ereg regs2 [Z_to_bv 64 sa]) (ms_mem (restrict (w_H W) ms)) rg)
      by (apply (w6c_region_nth _ ssf _ 0 rg HS); vm_compute; reflexivity)
  end
end.
cbn [sv_denot] in R20, R25.
rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in R20.
rewrite (ew_Ereg_nat regs2 _ 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in R25.
assert (E24 : getr regs2 24 = w64 cur') by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) H24).
rewrite E24 in R25.
assert (Hn20 : getr regs2 20 = w64 nl').
{ exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) H20). }
assert (Hslot : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xf8) 8 (nl' mod 2 ^ 64)).
{ apply (w6c_field _ _ 9%nat R _ _ _ _ _ 0xf8 8 (SOff 20 0) (nl' mod 2 ^ 64) HR0 U9).
  - cbv [In]. tauto.
  - cbn [sv_denot]. rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), Z.add_0_r, Hn20. unfold w64.
    rewrite Z_to_bv_unsigned. reflexivity.
  - cbn. apply Z.mod_pos_bound. lia.
  - cbn. lia. }
eapply (w6c_leaf STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F _ cur' nl' sa _ _ _ _ HS).
- reflexivity.
- vm_compute. reflexivity.
- exact HJ2.
- eapply same_io_trans; [exact Hio2 | apply RPgCfgChanges.same_io_wvb].
- intros r Hr. rewrite (regs_kept_of_st_ok rsegs _ _ ms regs2 [Z_to_bv 64 sa] (w_H W) [10; 11; 12; 13; 14; 15; 16; 17; 20; 25]%bv HS
    (env_agree_refl _ _) ltac:(vm_compute; reflexivity) r).
  + exact (w6c_keep_saved regs regs2 HP2 r Hr).
  + cbv [w6c_keep In] in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; discriminate|]). destruct Hr.
  + cbv [w6c_keep In] in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hr.
- unfold w64. exact R20.
- exact R25.
- exact HM.
- rewrite <- (w6c_ent_set ty sz) by lia.
  apply (rm_bytes_kept rsegs (w_H W) mem2 (w_H W) (ms_mem ms)).
  2:{ intros x Hx. rewrite !length_app, !length_le32, length_zeros in Hx. apply HE3; lia. }
  rewrite <- (w6c_ow_zeros ty sz) by lia.
  apply (rm_bytes_patch rsegs (w_H W) memc (w_H W) mem2 (F + 0xf0) _ 8 (zeros (Z.to_nat sz)) He).
  + apply (rm_memset_bytes rsegs (w_H W) mem2 (F + 0xf0 + Z.of_nat 8) 0 (Z.to_nat sz)).
    intros i Hi. replace (F + 0xf0 + Z.of_nat 8 + i) with (F + 0xf8 + i) by lia. apply Heff. lia.
  + rewrite !length_app, !length_le32, !length_zeros. lia.
  + intros y Hy Hny. rewrite !length_app, !length_le32, !length_zeros in Hy.
    rewrite length_zeros, Nat2Z.inj_add, Z2Nat.id in Hny by lia.
    apply HK2; [lia | lia | unfold ESTACK in *; lia].
- exact Hslot.
Qed.
End d.
End b.
