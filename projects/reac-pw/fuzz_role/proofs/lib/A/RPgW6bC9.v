(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the block lemma w6b_c9 of
   lib/A/RPgW6bBase.v, ent_build's case 9 (the default arm of the `switch (kind % 10)`, pod.h:367-377) from its
   entry 0x81184 to the join J 0x8165c. Proves no function (kind: segment lemma).

   THE THREE PIECES.
     A  0x81184 .. the `jal` at 0x811ac (-> __asan_memcpy 0x510d4, which returns at 0x811b0):
          ld s4,0xf0(s1)             s4 := F + 0xf0 (&e)
          a0 := 14; sw a0,0(s4)      e.type       := POD_STRUCT
                    sw a0,8(s4)      e.body[0..4) := 14
          a0 := 8;  sw a0,0xc(s4)    e.body[4..8) := POD_STRING
          a1 := 0x21120 (ent_build.s); a2 := 14; a0 := [R+0x20] (= F + 0x100 = &e.body[8])
     B  __asan_memcpy(e.body + 8, ent_build.s, 14): the kernel's aintrin_realizes OCpy in its journal form
        (lib/A/RPgW7bKit.v w7_memcpy_at), a hypothesis of the proof. Every check of the copy is the callee's:
        [F+0x100, F+0x10e) is in scope and writable in the frame (3, pos) the harness holds (w6b_in's facts on e
        and lib/Reusable/YG0d.v's AR_frames_law), and the source is the registered global ent_build.s, its 13
        bytes and the NUL (w6b_s_ok = RPgBase.rl_cstr at 0x21120).
     C  0x811b0 .. J 0x8165c:
          a0 := 0x18; sw a0,4(s4)    e.size := 24
          sd s9,0xf8(s1)             [R+0xf8] := what is left after the kind byte
          j 0x81448; mv s9,s8 (the cursor); ld s4,0xb0(s1) (the shadow address back into s4); j J
   The case reads no input byte and its own code holds no instrumented check, so A and C are each one run of the
   plain engine over the code table of lib/A/RPgEntBKit.v.

   WHY A's STORES DO NOT DISTURB THE COPY'S CHECKS. A writes only e's first 16 bytes, which lie in the frame for
   locals, and that frame is application memory (AR_frames_law's in_app): it is either below the low shadow range
   or at or above kHighMemBeg. The shadow bytes the copy's checks read, and the shadow hull around them, lie in
   [kLowMemEnd - 7, kHighMemBeg + 7), so the two are apart in both cases (c9_ra_kept_app, c9_hull_kept_band).

   AT J. e holds le32 14 ++ le32 24 ++ le32 14 ++ le32 8 ++ "reac.cfg.rate" ++ NUL ++ 74 zero bytes: the four
   words A and C store, the 14 bytes the copy brings from ent_build.s, and the tail of the 104 zero bytes the
   memset of pod.h:279 left (w6b_in). That list is Layout.ent_mem of Model.ent_build's default pod,
   Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2). [R+0xf8] = |r|, what the model
   leaves; s9 = the cursor c; s4 = the shadow address vb. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgMem RPgSteps RPgW6aBase RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgEntBKit RPgW7bBase RPgW7bKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition C9_RET : Z := 0x811b0.      (* after the `jal` to __asan_memcpy at 0x811ac *)
(* the shadow band: kLowMemEnd - 7 and kHighMemBeg + 7, the hull's two ends *)
Definition C9_BLO : Z := 0x7fff7ff9.
Definition C9_BHI : Z := 0x10007fff8007.

(* ===================== block A's symbolic state =====================
   The registers are their own atoms; the extra atom 32 is F (the frame for locals).
     rRa  [R+0x20, R+0xf8)  read only, with the two cells the block loads:
          R+0x20 = F + 0x100 (&e.body[8]) and R+0xf0 = F + 0xf0 (&e)
     rEa  [F+0xf0, F+0x100) written: e.type and e.body[0..8)
   The block reads no shadow byte, so the engine asks no obligation. *)
Definition c9_rRa : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0xf8 0 0
  [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0x100)); YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0xf0))].
Definition c9_rEa : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0x100 0xf0 0x100 [].
Definition c9_factsA : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (32%nat, mkAF 4096 0x7fffff800000 4)] [] [].
Definition ss_c9A : sstate := mkSS W6B_D9 sr_atoms [c9_rRa; c9_rEa] None c9_factsA.
Definition c9_extraA (F : Z) : list word := [Z_to_bv 64 F].
Definition c9_wrA (F : Z) : Z -> Prop := fun a => F + 0xf0 <= a < F + 0x100.

(* ===================== block C's symbolic state =====================
   The extra atom 32 is the value of [R+0xb0] (the shadow address the case reloads into s4).
     rRc  [R+0xb0, R+0x100): the cell R+0xb0 read, the window [R+0xf8, R+0x100) written
     rEc  [s4+4, s4+8) = [F+0xf4, F+0xf8) written: e.size *)
Definition c9_rRc : YP09.region := YP09.mkRegion (Some 9%nat) 0xb0 0x100 0xf8 0x100
  [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))].
Definition c9_rEc : YP09.region := YP09.mkRegion (Some 20%nat) 4 8 4 8 [].
Definition c9_factsC : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (20%nat, mkAF 4336 0x7fffff800000 4)] [] [].
Definition ss_c9C : sstate := mkSS C9_RET sr_atoms [c9_rRc; c9_rEc] None c9_factsC.
Definition c9_extraC (vb : Z) : list word := [Z_to_bv 64 vb].
Definition c9_wrC (R F : Z) : Z -> Prop :=
  fun a => (F + 0xf4 <= a < F + 0xf8) \/ (R + 0xf8 <= a < R + 0x100).

(* ======================================== the model ======================================== *)
Lemma c9_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 9 ->
  ent_build (b :: r) = (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2), r).
Proof.
intros b r H. unfold ent_build, Cursor.fuzz_u8. cbv beta iota. rewrite H. reflexivity.
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c9_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c9_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c9_reg_eq : forall (regs regs' : bvmap 5 word) (r : bv 5),
getr regs' (Z_to_bv 5 (bv_unsigned r)) = getr regs (Z_to_bv 5 (bv_unsigned r)) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma c9_den_off : forall E n (v o : Z), bv_unsigned (ew E n) = v -> sv_denot E (SOff n o) = Z_to_bv 64 (v + o).
Proof. intros E n v o H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

(* every register outside w6b_clob is callee-saved: the call in the middle of the case keeps it *)
Lemma c9_clob_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6b_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn. pose proof (u5_range r) as Hb.
assert (HI : forall z, bv_unsigned r = z -> In (Z_to_bv 5 z) w6b_clob -> False).
{ intros z Hz Hmem. apply Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r), Hz. exact Hmem. }
unfold acallee_saved.
assert (H : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
  bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 10 \/ bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/
  bv_unsigned r = 15 \/ bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/
  bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/
  bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat (destruct H as [H|H];
  [ first [ lia
          | destruct (HI _ H ltac:(unfold w6b_clob; cbv [In];
              repeat (first [left; apply bv_eq; reflexivity | right]))) ]
  | ]).
first [ lia
      | destruct (HI _ H ltac:(unfold w6b_clob; cbv [In];
          repeat (first [left; apply bv_eq; reflexivity | right]))) ].
Qed.

(* ---- where the shadow bytes of an address below kHighMemEnd, and their hull, lie ---- *)
Lemma c9_shof_lo : forall x, 0 <= x -> 0x7fff8000 <= shadow_of_addr SHADOW_OFF x.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma c9_shof_hi : forall x, 0 <= x < 2 ^ 47 -> shadow_of_addr SHADOW_OFF x < 0x10007fff8000.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma c9_sh_lo : forall x, 0 <= x -> C9_BLO <= shadow_addr x / 8 * 8.
Proof.
intros x Hx. unfold C9_BLO, shadow_addr, SHADOW_OFF.
assert (D : 0 <= x / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_mod (0x7fff8000 + x / 8) 8 ltac:(lia)) as M.
pose proof (Z.mod_pos_bound (0x7fff8000 + x / 8) 8 ltac:(lia)) as P. lia.
Qed.
Lemma c9_sh_hi : forall x, 0 <= x < 2 ^ 47 -> shadow_addr x / 8 * 8 + 8 <= C9_BHI.
Proof.
intros x Hx. unfold C9_BHI, shadow_addr, SHADOW_OFF.
assert (D : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (D0 : 0 <= x / 8) by (apply Z.div_pos; lia).
pose proof (Z.mul_div_le (0x7fff8000 + x / 8) 8 ltac:(lia)) as L. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- rm_bytes plumbing ---- *)
Lemma c9_app : forall H mem a l1 l2 n a2, Z.of_nat (length l1) = n -> a2 = a + n ->
  rm_bytes rsegs H mem a l1 -> rm_bytes rsegs H mem a2 l2 -> rm_bytes rsegs H mem a (l1 ++ l2).
Proof.
intros H mem a l1 l2 n a2 Hn -> B1 B2. apply rm_bytes_app. split; [exact B1|]. rewrite Hn. exact B2.
Qed.
Lemma c9_zeros : forall H mem a n,
  (forall i, 0 <= i < Z.of_nat n -> mbyte rsegs (mrestrict H mem) (a + i) = Some (Z_to_bv 8 0)) ->
  rm_bytes rsegs H mem a (zeros n).
Proof.
intros H mem a n Hz. apply rm_bytes_aview. intros i Hi. rewrite length_zeros in Hi.
unfold zeros. rewrite (rm_nth_repeat NUL (Z_to_bv 8 0) n i Hi).
unfold aview. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma c9_val_kept : forall (W : world rsegs) m m' a n v,
  val_mem rsegs (mrestrict (w_H W) m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x) ->
  val_mem rsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v V K. apply (rm_val_of_bytes rsegs (w_H W) m').
apply (rm_bytes_kept rsegs (w_H W) m); [apply rm_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.

(* A range stays addressable, and its shadow hull stays visible, when the bytes that changed all lie outside
   the shadow band [C9_BLO, C9_BHI): a write inside a frame for locals (in_app) is such a write. *)
Lemma c9_ra_kept_app : forall (W : world rsegs) m m' (Wr : Z -> Prop) a n,
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
(forall x, 0 <= x < 2 ^ 64 -> ~ Wr x -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x) ->
(forall x, Wr x -> x < C9_BLO \/ C9_BHI <= x) -> 0 <= a -> a + n <= 2 ^ 47 ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' Wr a n HR HK HW Ha Han. apply (rm_ra_kept rsegs (w_H W) m (w_H W) m'); [exact HR|].
intros x Hx.
pose proof (c9_shof_lo x ltac:(lia)) as L. pose proof (c9_shof_hi x ltac:(lia)) as U.
apply HK; [lia|]. intros Hwr. pose proof (HW _ Hwr) as HB. unfold C9_BLO, C9_BHI in HB. lia.
Qed.
Lemma c9_hull_kept_band : forall (W : world rsegs) m m' (Wr : Z -> Prop) a n,
shadow_hull_vis (aview rsegs (w_H W) m) a n ->
(forall x, 0 <= x < 2 ^ 64 -> ~ Wr x -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x) ->
(forall x, Wr x -> x < C9_BLO \/ C9_BHI <= x) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
shadow_hull_vis (aview rsegs (w_H W) m') a n.
Proof.
intros W m m' Wr a n HV HK HW Ha Han Hn. apply (rm_hull_kept rsegs (w_H W) m (w_H W) m'); [exact HV|].
intros s Hs Hne. pose proof (c9_sh_lo a ltac:(lia)) as L. pose proof (c9_sh_hi (a + n - 1) ltac:(lia)) as U.
unfold C9_BLO in L. unfold C9_BHI in U.
rewrite HK; [exact Hne | lia |]. intros Hwr. pose proof (HW _ Hwr) as HB.
unfold C9_BLO, C9_BHI in HB. lia.
Qed.

(* the register r of the engine's last state, as its symbolic value's denotation *)
Ltac c9_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.
Ltac c9_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac c9_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; c9_kio].

(* a chunk of region i of the state a run ended in, at an absolute address *)
Lemma c9_val_at : forall E ss (H : word -> bool) ms i rg off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks rg) -> base_val E (YP09.r_base rg) = b ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i rg off n e v b a HS Hi Hc Hb He Hv Hn ->.
pose proof (eb_region E ss (restrict H ms) rg HS (nth_error_In _ _ Hi)) as Hok.
rewrite <- Hb. exact (eb_chunk_val E _ rg off n e v Hok Hc He Hv Hn).
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.

(* ===================== block A: 0x81184 -> __asan_memcpy 0x510d4 ===================== *)
Lemma c9_A_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1a0 <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= F -> F + 512 <= alloc_ceiling -> F + 512 <= R -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x20) 8 (F + 0x100) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (F + 0xf0) ->
(forall a, F + 0xf0 <= a < F + 0x100 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (c9_extraA F)) ss_c9A
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D9) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F H9 HR1 HR2 HR16 HF1 HF2 HFR HF32 V20 Vf0 Pe.
pose proof asan_consts as (Hceil0 & _).
rewrite restrict_mkst_fx. set (E := Ereg regs (c9_extraA F)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth c9_extraA]. apply unsigned_lit_small. lia. }
assert (HF16 : F mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (2 * q). lia. }
unfold ss_c9A. apply (entry_st_ok_full rsegs); try change (Ereg regs (c9_extraA F)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold YP09.region_ok, c9_rRa.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val rsegs E _ R 0x20 8 (SOff 32 0x100) (F + 0x100));
        [exact (c9_den_off E 32 F 0x100 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact V20].
    * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 32 0xf0) (F + 0xf0));
        [exact (c9_den_off E 32 F 0xf0 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0].
  + unfold YP09.region_ok, c9_rEa.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply Pe. lia.
- unfold c9_rRa, c9_rEa. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. cbn [c9_factsA f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U9, U32. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Lemma c9_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1a0 <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= F -> F + 512 <= alloc_ceiling -> F + 512 <= R -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x20) 8 (F + 0x100) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (F + 0xf0) ->
(forall a, F + 0xf0 <= a < F + 0x100 -> apresent (w_H W) memc a) ->
(forall a, F + 0xf0 <= a < F + 0x100 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (cfg_at rsegs W6B_D9 regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc
  [1; 10; 11; 12; 20]%bv (c9_wrA F)
  (fun regs2 mem2 => getr regs2 1 = w64 C9_RET /\ getr regs2 10 = w64 (F + 0x100) /\
     getr regs2 11 = w64 W6B_S /\ getr regs2 12 = w64 14 /\ getr regs2 20 = w64 (F + 0xf0) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 14 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf8) 4 14 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xfc) 4 8)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F
  HJ H9 HR1 HR2 HR16 HF1 HF2 HFR HF32 V20 Vf0 Pe HWR.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof asan_consts as (Hceil0 & _).
set (E := Ereg regs (c9_extraA F)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth c9_extraA]. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs E ss_c9A (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D9) memc (seg_rom rsegs))))
  by exact (c9_A_entry W regs memc R F H9 HR1 HR2 HR16 HF1 HF2 HFR HF32 V20 Vf0 Pe).
unfold cfg_at.
aj_run_to eb_tbl_ok HS HJ W7_MEMCPY.
- lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp fp b0 bc lyx ow) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
    [ reflexivity | exact U32
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWR; lia
    | apply awr_ok_nil ].
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c9_kio | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs (c9_extraA F) (w_H W) _ HS);
      [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (RPgCfgChanges.kept_run (c9_wrA F) _ _ (w_H W) memc memc (ms_mem ms)
      (fun x _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (rg & Hin & Hb). cbv beta.
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    unfold c9_wrA. destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U32 in Hb; lia.
  + cbv beta.
    split; [c9_reg HS; reflexivity|].
    split; [c9_reg HS; rewrite (c9_den_off E 32 F 0x100 U32); reflexivity|].
    split; [c9_reg HS; reflexivity|].
    split; [c9_reg HS; reflexivity|].
    split; [c9_reg HS; rewrite (c9_den_off E 32 F 0xf0 U32); reflexivity|].
    split; [eapply (c9_val_at E _ (w_H W) ms 1%nat _ 0xf0 4%N _ 14 F (F + 0xf0));
            [exact HS | reflexivity | c9_in | cbn [YP09.r_base base_val]; exact U32
            | reflexivity | cbn; lia | lia | lia]|].
    split; [eapply (c9_val_at E _ (w_H W) ms 1%nat _ 0xf8 4%N _ 14 F (F + 0xf8));
            [exact HS | reflexivity | c9_in | cbn [YP09.r_base base_val]; exact U32
            | reflexivity | cbn; lia | lia | lia]|].
    eapply (c9_val_at E _ (w_H W) ms 1%nat _ 0xfc 4%N _ 8 F (F + 0xfc));
      [exact HS | reflexivity | c9_in | cbn [YP09.r_base base_val]; exact U32
      | reflexivity | cbn; lia | lia | lia].
Qed.

(* ===================== block C: 0x811b0 -> J 0x8165c ===================== *)
Lemma c9_C_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F vb,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1a0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 20 = w64 (F + 0xf0) -> 4096 <= F -> F + 512 <= alloc_ceiling -> F + 512 <= R -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 vb -> 0 <= vb < 2 ^ 64 ->
(forall a, R + 0xf8 <= a < R + 0x100 -> apresent (w_H W) memc a) ->
(forall a, F + 0xf4 <= a < F + 0xf8 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (c9_extraC vb)) ss_c9C
  (restrict (w_H W) (mkst regs (Z_to_bv 64 C9_RET) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F vb H9 HR1 HR2 HR16 H20 HF1 HF2 HFR HF32 Vb0 Hvb PR PE.
pose proof asan_consts as (Hceil0 & _).
rewrite restrict_mkst_fx. set (E := Ereg regs (c9_extraC vb)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U20 : bv_unsigned (ew E 20) = F + 0xf0)
  by exact (eb_U_reg regs _ 20 20%bv (F + 0xf0) eq_refl H20 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = vb).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth c9_extraC]. apply unsigned_lit_small. lia. }
assert (HF16 : (F + 0xf0) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (2 * q + 15). lia. }
unfold ss_c9C. apply (entry_st_ok_full rsegs); try change (Ereg regs (c9_extraC vb)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold YP09.region_ok, c9_rRc.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply PR; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs E _ R 0xb0 8 (SOff 32 0) vb);
      [rewrite (c9_den_off E 32 vb 0 U32); f_equal; lia
      | change (8 * Z.of_N 8) with 64; lia | lia | exact Vb0].
  + unfold YP09.region_ok, c9_rEc.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply PE. lia.
- unfold c9_rRc, c9_rEc. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. cbn [c9_factsC f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U9, U20. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Lemma c9_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F vb c n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1a0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 20 = w64 (F + 0xf0) -> 4096 <= F -> F + 512 <= alloc_ceiling -> F + 512 <= R -> F mod 32 = 0 ->
getr regs 24 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 25 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 vb -> 0 <= vb < 2 ^ 64 ->
(forall a, R + 0xf8 <= a < R + 0x100 -> apresent (w_H W) memc a) ->
(forall a, F + 0xf4 <= a < F + 0xf8 -> apresent (w_H W) memc a) ->
(forall a, R + 0xf8 <= a < R + 0x100 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
(forall a, F + 0xf4 <= a < F + 0xf8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (cfg_at rsegs C9_RET regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W6_J regs memc mdc
  [10; 20; 25]%bv (c9_wrC R F)
  (fun regs2 mem2 => getr regs2 20 = w64 vb /\ getr regs2 25 = w64 c /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 n /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 24)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F vb c n
  HJ H9 HR1 HR2 HR16 H20 HF1 HF2 HFR HF32 H24 Hc H25 Hn Vb0 Hvb PR PE HWR HWE.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof asan_consts as (Hceil0 & _).
set (E := Ereg regs (c9_extraC vb)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U20 : bv_unsigned (ew E 20) = F + 0xf0)
  by exact (eb_U_reg regs _ 20 20%bv (F + 0xf0) eq_refl H20 ltac:(lia)).
assert (U24 : bv_unsigned (ew E 24) = c) by exact (eb_U_reg regs _ 24 24%bv c eq_refl H24 ltac:(lia)).
assert (U25 : bv_unsigned (ew E 25) = n) by exact (eb_U_reg regs _ 25 25%bv n eq_refl H25 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = vb).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth c9_extraC]. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs E ss_c9C (restrict (w_H W) (mkst regs (Z_to_bv 64 C9_RET) memc (seg_rom rsegs))))
  by exact (c9_C_entry W regs memc R F vb H9 HR1 HR2 HR16 H20 HF1 HF2 HFR HF32 Vb0 Hvb PR PE).
unfold cfg_at.
aj_run_to eb_tbl_ok HS HJ W6_J.
- lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp fp b0 bc lyx ow) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R);
    [ reflexivity | exact U9
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWR; lia | ].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (F + 0xf0));
    [ reflexivity | exact U20
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWE; lia
    | apply awr_ok_nil ].
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c9_kio | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs (c9_extraC vb) (w_H W) _ HS);
      [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (RPgCfgChanges.kept_run (c9_wrC R F) _ _ (w_H W) memc memc (ms_mem ms)
      (fun x _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (rg & Hin & Hb). cbv beta.
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    unfold c9_wrC. destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U20 in Hb;
      first [right; lia | left; lia].
  + cbv beta.
    split; [c9_reg HS; rewrite (c9_den_off E 32 vb 0 U32); unfold w64; f_equal; lia|].
    split; [c9_reg HS; rewrite (c9_den_off E 24 c 0 U24); unfold w64; f_equal; lia|].
    split; [eapply (c9_val_at E _ (w_H W) ms 0%nat _ 0xf8 8%N _ n R (R + 0xf8));
            [exact HS | reflexivity | c9_in | cbn [YP09.r_base base_val]; exact U9
            | rewrite (c9_den_off E 25 n 0 U25); f_equal; lia
            | cbn; lia | lia | lia]|].
    eapply (c9_val_at E _ (w_H W) ms 1%nat _ 4 4%N _ 24 (F + 0xf0) (F + 0xf4));
      [exact HS | reflexivity | c9_in | cbn [YP09.r_base base_val]; exact U20
      | reflexivity | cbn; lia | lia | lia].
Qed.

(* ===================== the case ===================== *)
Theorem w6b_c9 : w6b_c9_stmt B MT.
Proof using MTL LAWS MCPY.
unfold w6b_c9_stmt, w6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r
  (HJ & HR16 & HRhi & HRlo & Hown & HF & Hrom) Hcase Hin HSok.
cbv beta in Hcase.
pose proof asan_consts as (Hceil0 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
(* ---- what the entry state gives ---- *)
destruct Hin as (G2 & G3 & G4 & G9 & G23 & G24 & G14 & G25 & G21 & G27 & _ & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 &
  V80 & Hvb & Hkdr & Hpp1 & Hpp2 & HF1 & HFceil & HF32 & Ez & Hra104 & Hhull104 & Hc1 & Hin6 & _ & _).
pose proof Hin6 as (Hgarr & Hrain & Hcur0 & Hcurn & Hamr & Hout).
(* ---- the journal's static facts ---- *)
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HRceil : alloc_ceiling + 16384 <= R) by lia.
assert (HRlo2 : 0x7fff7f800000 <= R) by lia.
assert (HRhi2 : R + 0x1a0 <= 2 ^ 47) by lia.
assert (HFR : F + 512 <= R) by lia.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & HFapp & HFpres & _).
rewrite <- HF in HFapp, HFpres.
change (fs_frame_bytes 3) with 512 in HFapp, HFpres.
(* the frame is writable for the journal, and no byte of it is in the image *)
assert (HWF : forall a, F <= a < F + 512 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. right. right. right. exists 3, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 3) with 512. lia. }
assert (HFimg : forall a, F <= a < F + 512 -> ~ in_img rsegs a).
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR _)).
  right. left. exists 3, pos. split; [exact Hin3|].
  rewrite <- HF. change (fs_frame_bytes 3) with 512. lia. }
(* e's bytes are application memory, so they lie outside the shadow band *)
assert (HWband : forall x, c9_wrA F x -> x < C9_BLO \/ C9_BHI <= x).
{ intros x Hx. unfold c9_wrA in Hx. unfold C9_BLO, C9_BHI.
  destruct HFapp as (_ & [Hl | (Hh & _)]);
    [ left; unfold kLowShadowBeg in Hl; lia | right; unfold kHighMemBeg in Hh; lia ]. }
assert (HAMD : amem_range (F + 0x100) 14).
{ unfold amem_range. destruct HFapp as (_ & [Hl | (Hh & _)]);
    [ left; unfold kLowMemEnd; unfold kLowShadowBeg in Hl; lia
    | right; split; [unfold kHighMemBeg in Hh |- *; lia | unfold kHighMemEnd; lia] ]. }
(* ---- ent_build.s, the source of the copy ---- *)
unfold w6b_s_ok in HSok.
pose proof HSok as (HSb & HSz & _ & HS0 & HS63 & HSimg & HSamr & HSra & HShull).
rewrite length_map in HSb, HSz, HSimg, HSamr, HSra, HShull.
assert (LS9 : length S9 = 13%nat) by reflexivity.
rewrite LS9 in HSb, HSz, HSimg, HSamr, HSra, HShull.
change (Z.of_nat 13) with 13 in HSz, HSimg, HSamr, HSra, HShull.
assert (HSFd : W6B_S + 14 <= F \/ F + 512 <= W6B_S).
{ assert (A0 : ~ (F <= W6B_S + 0 < F + 512)) by (intros X; apply (HFimg _ X); apply HSimg; lia).
  assert (A1 : ~ (F <= W6B_S + 13 < F + 512)) by (intros X; apply (HFimg _ X); apply HSimg; lia).
  lia. }
assert (HSrc : rm_bytes rsegs (w_H W) memc W6B_S (S9 ++ [NUL])).
{ apply rm_bytes_aview. intros i Hi. rewrite length_app, LS9 in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i 13) as [H1|H1].
  - rewrite app_nth1 by lia. specialize (HSb (Z.of_nat i) ltac:(lia)).
    rewrite Nat2Z.id, rm_nth_map in HSb. exact HSb.
  - assert (Ei : i = 13%nat) by lia. subst i.
    rewrite app_nth2 by lia. rewrite LS9. cbn [Nat.sub nth].
    change (Z.of_nat 13) with 13. rewrite HSz. reflexivity. }
(* ---- block A ---- *)
eapply SRr_bind.
{ apply (c9_A STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F HJ G9); try lia.
  - exact V20.
  - exact Vf0.
  - intros a Ha. apply (proj1 (HFpres a ltac:(lia))).
  - intros a Ha. apply HWF. lia. }
cbv beta. intros W1 c1 _ (-> & regsA & memA & mdA & -> & HJA & HioA & HrA & HKA & HprA &
  (A1 & A10 & A11 & A12 & A20 & VA0 & VA8 & VAc)).
(* the registers block A kept *)
assert (A2 : getr regsA 2 = w64 R)
  by (rewrite (HrA 2%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G2).
assert (A3 : getr regsA 3 = w64 (as_gp B))
  by (rewrite (HrA 3%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G3).
assert (A4 : getr regsA 4 = w64 (as_tp B))
  by (rewrite (HrA 4%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G4).
assert (A9 : getr regsA 9 = w64 R)
  by (rewrite (HrA 9%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G9).
assert (A24 : getr regsA 24 = w64 c)
  by (rewrite (HrA 24%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G24).
assert (A25 : getr regsA 25 = w64 (Z.of_nat (length r)))
  by (rewrite (HrA 25%bv ltac:(apply c9_nz; vm_compute; reflexivity)
        ltac:(apply c9_notin; vm_compute; reflexivity)); exact G25).
assert (Asp : spZ regsA = sp0 + (R - sp0))
  by (unfold spZ; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (KcA : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0x100) ->
  aview rsegs (w_H W) memA a = aview rsegs (w_H W) memc a) by exact HKA.
(* ---- the memcpy's premises at memA ---- *)
assert (RAD : range_addressable (aview rsegs (w_H W) memA) SHADOW_OFF (F + 0x100) 14).
{ apply (c9_ra_kept_app W memc memA (c9_wrA F)); try lia.
  - apply (ra_sub _ _ (F + 0xf0) 104); [exact Hra104 | lia | lia].
  - exact HKA.
  - exact HWband. }
assert (RAS : range_addressable (aview rsegs (w_H W) memA) SHADOW_OFF W6B_S 14).
{ apply (c9_ra_kept_app W memc memA (c9_wrA F)); try (unfold W6B_S; lia).
  - exact HSra.
  - exact HKA.
  - exact HWband. }
assert (HUD : shadow_hull_vis (aview rsegs (w_H W) memA) (F + 0x100) 14).
{ apply (c9_hull_kept_band W memc memA (c9_wrA F)); try lia.
  - apply (rm_hull_sub _ (F + 0xf0) 104); [exact Hhull104 | lia | lia | lia].
  - exact HKA.
  - exact HWband. }
assert (HUS : shadow_hull_vis (aview rsegs (w_H W) memA) W6B_S 14).
{ apply (c9_hull_kept_band W memc memA (c9_wrA F)); try (unfold W6B_S; lia).
  - exact HShull.
  - exact HKA.
  - exact HWband. }
assert (HSrcA : rm_bytes rsegs (w_H W) memA W6B_S (S9 ++ [NUL])).
{ apply (rm_bytes_kept rsegs (w_H W) memc); [exact HSrc|].
  intros x Hx. rewrite length_app, LS9 in Hx. cbn [length] in Hx.
  apply KcA; unfold W6B_S in *; lia. }
assert (HSnn : forall x, W6B_S <= x < W6B_S + 14 -> aview rsegs (w_H W) memA x <> None).
{ intros x Hx. replace x with (W6B_S + Z.of_nat (Z.to_nat (x - W6B_S))) by lia.
  rewrite (proj1 (rm_bytes_aview rsegs (w_H W) memA W6B_S (S9 ++ [NUL])) HSrcA (Z.to_nat (x - W6B_S))
    ltac:(rewrite length_app, LS9; cbn [length]; lia)).
  discriminate. }
eapply SRr_bind.
{ apply (w7_memcpy_at B LAWS MCPY W regsA memA STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdA k
    (F + 0x100) W6B_S 14 (R - sp0) (w64 C9_RET) HJA A10 A11 A12).
  - lia.
  - lia.
  - lia.
  - exact Asp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - lia.
  - exact A3.
  - exact A4.
  - exact A1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [apply HWF; lia|]. rewrite HE. lia.
  - exact HAMD.
  - exact RAD.
  - intros _. exact HUD.
  - unfold W6B_S. lia.
  - unfold W6B_S. lia.
  - intros a Ha. split; [apply HSnn; lia|].
    rewrite Asp. replace (sp0 + (R - sp0)) with R by lia. rewrite HE. unfold W6B_S in *. lia.
  - lia.
  - unfold amem_range. left. unfold W6B_S, kLowMemEnd. lia.
  - exact RAS.
  - intros _. exact HUS. }
cbv beta. intros W2 c2 _ (-> & regsB & memB & mdB & -> & HJB & HioB & HPB & B10 & HD & HKB & HprB).
(* the registers the call kept *)
assert (B9 : getr regsB 9 = w64 R)
  by (rewrite (c9_reg_eq regsA regsB 9%bv (HPB 9 ltac:(unfold acallee_saved; lia))); exact A9).
assert (B20 : getr regsB 20 = w64 (F + 0xf0))
  by (rewrite (c9_reg_eq regsA regsB 20%bv (HPB 20 ltac:(unfold acallee_saved; lia))); exact A20).
assert (B24 : getr regsB 24 = w64 c)
  by (rewrite (c9_reg_eq regsA regsB 24%bv (HPB 24 ltac:(unfold acallee_saved; lia))); exact A24).
assert (B25 : getr regsB 25 = w64 (Z.of_nat (length r)))
  by (rewrite (c9_reg_eq regsA regsB 25%bv (HPB 25 ltac:(unfold acallee_saved; lia))); exact A25).
assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x100 <= a < F + 0x10e) -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W) memB a = aview rsegs (w_H W) memA a).
{ intros a Ha H1 H2. apply HKB; [exact Ha | lia | rewrite HE; lia]. }
(* ---- block C ---- *)
eapply SRr_bind.
{ apply (c9_C STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB mdB k regsB R F vb c
    (Z.of_nat (length r)) HJB B9); try lia.
  - exact B20.
  - exact B24.
  - exact B25.
  - apply (c9_val_kept W memc memB (R + 0xb0) 8 vb); [exact Vb0|].
    intros x Hx. rewrite KAB by lia. apply KcA; lia.
  - intros a Ha. apply HprB. apply HprA. apply Hpres. lia.
  - intros a Ha. apply HprB. apply HprA. apply (proj1 (HFpres a ltac:(lia))).
  - intros a Ha. left. lia.
  - intros a Ha. apply HWF. lia. }
cbv beta. intros W3 c3 _ (-> & regsC & memC & mdC & -> & HJC & HioC & HrC & HKC & HprC &
  (C20 & C25 & VCf8 & VCf4)).
(* ---- the post at J ---- *)
apply SRr_ret. unfold w6_post.
exists lyc, Sc, regsC, memC, mdC.
split; [reflexivity|].
split; [exact HJC|].
(* every register the three pieces keep *)
assert (Hkeep3 : forall rg : bv 5, bv_unsigned rg <> 0 -> acallee_saved (bv_unsigned rg) ->
  ~ In rg [1; 10; 11; 12; 20]%bv -> ~ In rg [10; 20; 25]%bv -> getr regsC rg = getr regs rg).
{ intros rg Hr0 Hcs Hn1 Hn2.
  rewrite (HrC rg Hr0 Hn2), (c9_reg_eq regsA regsB rg (HPB (bv_unsigned rg) Hcs)).
  exact (HrA rg Hr0 Hn1). }
assert (Hsub1 : forall rg : bv 5, ~ In rg w6b_clob -> ~ In rg [1; 10; 11; 12; 20]%bv).
{ intros rg Hn X. apply Hn. unfold w6b_clob. cbv [In] in X |- *.
  repeat (destruct X as [X|X]; [rewrite <- X; repeat (first [left; reflexivity | right])|]). destruct X. }
assert (Hsub2 : forall rg : bv 5, ~ In rg w6b_clob -> ~ In rg [10; 20; 25]%bv).
{ intros rg Hn X. apply Hn. unfold w6b_clob. cbv [In] in X |- *.
  repeat (destruct X as [X|X]; [rewrite <- X; repeat (first [left; reflexivity | right])|]). destruct X. }
assert (Hkept : forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg w6b_clob -> getr regsC rg = getr regs rg)
  by (intros rg H1 H2; exact (Hkeep3 rg H1 (c9_clob_cs rg H1 H2) (Hsub1 rg H2) (Hsub2 rg H2))).
assert (E21 : bv_unsigned (21%bv : bv 5) = 21) by reflexivity.
assert (E27 : bv_unsigned (27%bv : bv 5) = 27) by reflexivity.
split; [exact Hkept|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [eapply same_io_trans; [exact HioA | exact HioB] | exact HioC]|].
split; [apply mo_le_refl; assumption|].
(* every byte outside w6b_wr kept, and the tail of e kept *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0x158) ->
  ~ (R - T_SEG_STK <= a < R) -> ~ (R + 0xf8 <= a < R + 0x100) ->
  aview rsegs (w_H W) memC a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H2 H3. rewrite Has in H2.
  rewrite (HKC a Ha ltac:(unfold c9_wrC; lia)). rewrite KAB by lia. apply KcA; lia. }
assert (KE : forall a, F + 0x10e <= a < F + 0x158 ->
  aview rsegs (w_H W) memC a = aview rsegs (w_H W) memc a).
{ intros a Ha. rewrite (HKC a ltac:(lia) ltac:(unfold c9_wrC; lia)).
  rewrite KAB by lia. apply KcA; lia. }
split.
{ intros a Ha Hnw. unfold w6b_wr in Hnw.
  assert (N1 : ~ (F + 0xf0 <= a < F + 0x158)) by (intros X; apply Hnw; right; right; right; exact X).
  assert (N2 : ~ (R - T_SEG_STK <= a < R)) by (intros X; apply Hnw; left; exact X).
  assert (N3 : ~ (R + 0xf8 <= a < R + 0x100)) by (intros X; apply Hnw; right; right; left; exact X).
  exact (KALL a Ha N1 N2 N3). }
(* ---- the state at J ---- *)
unfold w6b_J_R. rewrite (c9_model b r Hcase). cbn [fst snd].
split; [exact C20|].
split; [rewrite (Hkeep3 21%bv ltac:(apply c9_nz; vm_compute; reflexivity)
          ltac:(unfold acallee_saved; rewrite E21; lia)
          ltac:(apply c9_notin; vm_compute; reflexivity)
          ltac:(apply c9_notin; vm_compute; reflexivity)); exact G21|].
split; [rewrite (Hkeep3 27%bv ltac:(apply c9_nz; vm_compute; reflexivity)
          ltac:(unfold acallee_saved; rewrite E27; lia)
          ltac:(apply c9_notin; vm_compute; reflexivity)
          ltac:(apply c9_notin; vm_compute; reflexivity)); exact G27|].
split; [rewrite C25; unfold w64; f_equal; lia|].
split; [exact VCf8|].
(* e holds Layout.ent_mem of the default pod *)
assert (EM : ent_mem (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2)) =
  Z_to_le_bytes 4 14 ++ Z_to_le_bytes 4 24 ++ Z_to_le_bytes 4 14 ++ Z_to_le_bytes 4 8 ++
  (S9 ++ [NUL]) ++ zeros 74) by (vm_compute; reflexivity).
assert (Hfin : rm_bytes rsegs (w_H W) memC (F + 0xf0)
  (ent_mem (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2)))).
{ rewrite EM.
  (* e.type = POD_STRUCT *)
  apply (c9_app _ _ _ _ _ 4 (F + 0xf4)); [reflexivity | lia | | ].
  { apply rm_bytes_of_val. apply (c9_val_kept W memB memC (F + 0xf0) 4 14);
      [apply (c9_val_kept W memA memB (F + 0xf0) 4 14);
        [exact VA0 | intros x Hx; apply KAB; lia]
      | intros x Hx; apply HKC; [lia | unfold c9_wrC; lia]]. }
  (* e.size = 24 *)
  apply (c9_app _ _ _ _ _ 4 (F + 0xf8)); [reflexivity | lia | | ].
  { apply rm_bytes_of_val. exact VCf4. }
  (* e.body[0..4) = 14 *)
  apply (c9_app _ _ _ _ _ 4 (F + 0xfc)); [reflexivity | lia | | ].
  { apply rm_bytes_of_val. apply (c9_val_kept W memB memC (F + 0xf8) 4 14);
      [apply (c9_val_kept W memA memB (F + 0xf8) 4 14);
        [exact VA8 | intros x Hx; apply KAB; lia]
      | intros x Hx; apply HKC; [lia | unfold c9_wrC; lia]]. }
  (* e.body[4..8) = POD_STRING *)
  apply (c9_app _ _ _ _ _ 4 (F + 0x100)); [reflexivity | lia | | ].
  { apply rm_bytes_of_val. apply (c9_val_kept W memB memC (F + 0xfc) 4 8);
      [apply (c9_val_kept W memA memB (F + 0xfc) 4 8);
        [exact VAc | intros x Hx; apply KAB; lia]
      | intros x Hx; apply HKC; [lia | unfold c9_wrC; lia]]. }
  (* e.body[8..22) = the 14 bytes of ent_build.s *)
  apply (c9_app _ _ _ _ _ 14 (F + 0x10e)); [reflexivity | lia | | ].
  { apply (rm_bytes_kept rsegs (w_H W) memB).
    - apply (rm_memcpy_bytes rsegs (w_H W) memA (w_H W) memB W6B_S (F + 0x100) (S9 ++ [NUL])).
      + exact HSrcA.
      + intros i Hi. apply HD. rewrite length_app, LS9 in Hi. cbn [length] in Hi. lia.
    - intros x Hx. rewrite length_app, LS9 in Hx. cbn [length] in Hx.
      apply HKC; [lia | unfold c9_wrC; lia]. }
  (* the tail of the 104 zero bytes the memset left *)
  apply (rm_bytes_kept rsegs (w_H W) memc).
  - apply c9_zeros. intros i Hi.
    replace (F + 0x10e + i) with (F + 0xf0 + (30 + i)) by lia. apply Ez. lia.
  - intros x Hx. rewrite length_zeros in Hx. apply KE. lia. }
exact Hfin.
Qed.

End d.
End b.

Print Assumptions w6b_c9.
