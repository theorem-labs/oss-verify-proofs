(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 528 of its 639 lines of code are new or changed and 1380 lines of the source are left out. *)
(* reac_segconf_find on fuzz_segconf.asan (image A), part 1 of its walk: everything but the strcmp call.
   The symbolic executor over the position-abstract listing (SegPaLib.v) runs the stretches; the inline check of
   c->n at 0x8952c-0x89538 is removed by the shadow token of the block [c, c + 16616) (PaShadow.v, the statement's
   sa_addr on c), so the error path (the call of errpath_load4 at 0x89590) is not reached. The loop at 0x89544 is
   cut at its head and the epilogue at 0x8956c is re-seeded from the four saved words of the frame.
   reac_segconf_find.v adds the call (RtString.astrcmp_realizes through PaArt's aj_art_at) and composes. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_lem reac_segconf_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- reader facts that need no machine state ---------- *)
Definition fnd_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma fnd_kept_trans : forall rd1 rd2 rd3 lo hi lo' hi',
fnd_kept rd1 rd2 lo hi -> fnd_kept rd2 rd3 lo' hi' -> lo <= lo' -> hi' <= hi -> fnd_kept rd1 rd3 lo hi.
Proof. intros rd1 rd2 rd3 lo hi lo' hi' H12 H23 Hl Hh a Ha Hn. rewrite (H23 a Ha) by lia. exact (H12 a Ha Hn). Qed.
Lemma fnd_bytes_kept : forall rd rd' lo hi p l, fnd_kept rd rd' lo hi -> sa_bytes rd p l ->
0 <= p -> p + Z.of_nat (length l) < 2 ^ 64 -> (p + Z.of_nat (length l) <= lo \/ hi <= p) -> sa_bytes rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hw i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma fnd_val_kept : forall rd rd' lo hi p n v, fnd_kept rd rd' lo hi -> sa_val rd p n v ->
0 <= p -> p + Z.of_nat n < 2 ^ 64 -> (p + Z.of_nat n <= lo \/ hi <= p) -> sa_val rd' p n v.
Proof. intros rd rd' lo hi p n v HK H Hp Hl Hw k Hk. rewrite (HK (p + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma fnd_addr_sub_hull : forall a b, a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8.
Proof. intros a b H. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia | apply shadow_mono; exact H]. Qed.
Lemma fnd_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* `blez rs` is `bge x0, rs`: taken exactly when the word is <= 0 *)
Lemma fnd_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64.
rewrite unsigned_lit_small by lia. unfold bv_lts. rewrite !signed_lit.
rewrite !zcanon_small by lia. rewrite !fnd_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
Lemma fnd_sa_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
sa_addr rd q' n'.
Proof.
intros rd q n q' n' (H0 & H1 & H2 & H3 & H4) Hq Hn' Hqn.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
split; [intros x Hx; apply H3; lia|].
intros Hp. specialize (H4 ltac:(lia)). unfold shadow_hull_vis in *. intros s Hs. apply H4.
pose proof (fnd_addr_sub_hull q q' Hq) as A1.
pose proof (fnd_addr_sub_hull (q' + n' - 1) (q + n - 1) ltac:(lia)) as A2. lia.
Qed.
Lemma fnd_addr_kept : forall rd rd' lo hi q n, fnd_kept rd rd' lo hi -> sa_addr rd q n ->
0 <= q -> q + n <= lo -> kHighShadowEnd <= lo -> q + n <= 2 ^ 47 -> lo < 2 ^ 64 -> sa_addr rd' q n.
Proof.
intros rd rd' lo hi q n HK (H0 & H1 & H2 & H3 & H4) Hq Hqn Hks Hq47 Hlo.
assert (HKa : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < 2 ^ 64) -> rd' a = rd a)
  by (intros a Ha Hn2; apply HK; [exact Ha | lia]).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [exact (range_addressable_kept_win rd rd' lo (2 ^ 64) q n HKa Hks H0 Hq47 H3)|].
intros Hp. exact (shadow_hull_vis_kept_win rd rd' lo (2 ^ 64) q n HKa Hks H0 Hq47 Hp (H4 Hp)).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the stack this call needs: its 32-byte frame and the window the strcmp wrapper asks for
   (RtString.astrcmp_realizes: ecall_pre_stk segs B (2 * ESTACK)). The number is the unit's own
   SegInstA.STK_reac_segconf_find; this walk defines no second copy of it. *)
#[local] Notation FND_STK := SegInstA.STK_reac_segconf_find.
(* the listing offsets of the cut points (BASE + AF_reac_segconf_find = 0x894ec) *)
Definition FND_LH : Z := 18448.   (* 0x89544, the loop head *)
Definition FND_RET : Z := 18460.  (* 0x89550, the return address of the strcmp call *)
Definition FND_EPI : Z := 18488.  (* 0x8956c, the epilogue, a0 already set *)
(* the frame: ra s0 s1 s2 saved at sp0-8 .. sp0-32 *)
Definition fnd_saved : list Z := [1; 8; 9; 18].
(* the callee-saved registers this function never touches: the cut carries them, one conjunct each (a list and
   `In` would put bv literals under vm_compute, which normalises their well-formedness proofs: 75 GB, measured) *)
Definition fnd_Bx : sv := SOff 32 0.
Definition fnd_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition fnd_SBF : afact := mkAF SB SB 0.
Definition fnd_NF : afact := mkAF 0 32 0.
(* c->n, the 4 bytes at c + 0x2c80 *)
Definition fnd_nreg : YP09.region :=
  YP09.mkRegion (Some 10%nat) 11392 11396 0 0 [YP09.mkChunk 11392 (CVal 4 (SOff 33 0))].
(* the block [c, c + 16616) is addressable: the token that removes the inline check *)
Definition fnd_SH : list shent := [mkSHE 10 0 16616].
Definition fnd_ss_entry : sstate :=
  mkSS AF_reac_segconf_find sr_atoms [stack_region 32; got_regionP; bcell_regionP 32; fnd_nreg] None
    (mkFacts [(2%nat, fnd_spF); (32%nat, fnd_SBF); (10%nat, PTR 0); (11%nat, PTR 0); (33%nat, fnd_NF)] [] []).
Definition fnd_estack : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    (map (fun j => YP09.mkChunk (24 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 4)).
Definition fnd_ss_epi : sstate := mkSS FND_EPI sr_atoms [fnd_estack] None (mkFacts [(2%nat, fnd_spF)] [] []).
Definition fnd_ss_LH : sstate := mkSS FND_LH sr_atoms [] None (mkFacts [(2%nat, fnd_spF)] [] []).

Lemma fnd_val_mem_of_sa : forall H mem0 a n v,
sa_val (aview SEGS H mem0) a n v -> val_mem SEGS (mrestrict H mem0) a n v.
Proof using.
intros H mem0 a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem0 _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma fnd_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof using.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.
(* the shadow token's premise, in the shape YCbn asks (fuzz_command's rce_shent_ok) *)
Lemma fnd_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x ->
0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
range_addressable (YCbn.rd_of SEGS m) SB (x + lo) (hi - lo) ->
(forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
YCbn.shent_ok SEGS fnd_Bx E m (mkSHE n lo hi).
Proof using.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold YCbn.shent_ok, YCbn.app_apart, fnd_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
  apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64)
  by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
Lemma fnd_sa_of_val_mem : forall H mem0 a n v,
val_mem SEGS (mrestrict H mem0) a n v -> sa_val (aview SEGS H mem0) a n v.
Proof using.
intros H mem0 a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
(* the memory a run left: a run whose regions have no write window changes nothing *)
Ltac fnd_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m
    | _ => idtac end end.
Ltac fnd_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : fnd_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac fnd_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : fnd_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
        destruct Hin
      | exact Hx0 | exact Hn0 ]) end.


Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* ---------- one call of reac_segconf_find ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (RLO RHI c name : Z) (rcs : rconf) (nm : list Z).
Hypothesis HPRE : afn_pre SEGS B FND_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis Hc64 : 0 <= c < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 name.
Hypothesis Hnm64 : 0 <= name < 2 ^ 64.
Hypothesis HQP : query_pre SEGS B ly S (rdW W mem) c name rcs nm.

Definition fnd_Q : world SEGS -> config -> Prop :=
apost_base SEGS B FND_STK [] regs ly S W mem md EV_reac_segconf_find
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (seg_spec.find_ptr c rcs nm) /\
 sa_kept SEGS W mem W' mem' regs FND_STK (fun _ => False) /\
 sa_noalloc B ly S ly' S').

Lemma fnd_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + FND_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\
alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + FND_STK <= spZ regs.
Proof using HPRE Hc64 Hnm64.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.

(* where c's block lies: inside the live heap block the statement names *)
Lemma fnd_c_facts : 4096 <= c /\ c + 16616 <= alloc_ceiling /\ c mod 16 = 0 /\
off_img c 16616 /\ (forall y, c <= y < c + 16616 -> ~ (SB <= y < SB + 2 ^ 44)).
Proof using HPRE HQP Hc64 Hnm64 LAWS.
pose proof HPRE as (HAR & _).
destruct HQP as (Hc0 & Hc16 & HRC & (b & m & Hin & Hb1 & Hb2) & HAD & _).
unfold seg_spec.SEG_C_SIZE in Hb2.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Hoff.
unfold off_img in Hoff |- *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
split; [lia|]. split; [lia|]. split; [exact Hc16|]. split; [lia|].
intros y Hy. unfold SB. lia.
Qed.

(* where the name lies: a heap block, a live side-stack frame, or the image *)
Lemma fnd_name_facts : 4096 <= name /\ name + (Z.of_nat (length nm) + 1) <= alloc_ceiling.
Proof using HPRE HQP Hc64 Hnm64 LAWS.
pose proof HPRE as (HAR & _).
destruct HQP as (_ & _ & _ & _ & _ & Hn0 & Hstr & Hloc & Had & Hlen).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hloc as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hfin & Hcid & Hf1 & Hf2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _). lia.
- pose proof (pa_img_range name (proj1 (Himg name ltac:(lia)))) as R1.
  pose proof (pa_img_range (name + Z.of_nat (length nm)) (proj1 (Himg (name + Z.of_nat (length nm)) ltac:(lia)))) as R2.
  unfold kImgEnd in R1, R2. lia.
Qed.

Lemma fnd_blk : exists bs, sa_bytes (rdW W mem) c bs /\ seg_spec.rconf_enc rcs bs /\
Z.of_nat (length bs) = 16616 /\ (length (rc_seg rcs) <= 32)%nat.
Proof using HQP.
destruct HQP as (_ & _ & (bs & HB & HE) & _).
destruct (seg_query_facts.sq_rconf_len rcs bs HE) as [L LS].
exists bs. split; [exact HB | split; [exact HE | split; [exact L | exact LS]]].
Qed.
Lemma fnd_n_le : (length (rc_seg rcs) <= 32)%nat.
Proof using HQP. destruct fnd_blk as (bs & _ & _ & _ & H). exact H. Qed.
Lemma fnd_blk_vis : forall a, c <= a < c + 16616 -> rdW W mem a <> None.
Proof using HQP Hc64 Hnm64.
intros a Ha. destruct fnd_blk as (bs & HB & _ & L & _).
replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia. rewrite HB by lia. discriminate.
Qed.
Lemma fnd_n_val : sa_val (rdW W mem) (c + seg_spec.RC_N) 4 (Z.of_nat (length (rc_seg rcs))).
Proof using HQP.
destruct fnd_blk as (bs & HB & HE & _). exact (proj1 (fnd_rc_n _ c bs rcs HB HE)).
Qed.
Lemma fnd_c_addr : sa_addr (rdW W mem) c 16616.
Proof using HQP. destruct HQP as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma fnd_name_addr : sa_addr (rdW W mem) name (Z.of_nat (length nm) + 1).
Proof using HQP. destruct HQP as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma fnd_name_str : sa_str (rdW W mem) name nm.
Proof using HQP. destruct HQP as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma fnd_name_len : Z.of_nat (length nm) + 1 < 2 ^ 32.
Proof using HQP. destruct HQP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* the saved words of the frame *)
Definition fnd_frame (rd : reader) : Prop :=
forall j r, nth_error fnd_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a cut point: the journal from the entry, the memory outside the stack window unchanged, the frame, sp, and
   the callee-saved registers this function never touches *)
Definition fnd_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B FND_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
fnd_kept (rdW W mem) (rdW W mem1) (spZ regs - FND_STK) (spZ regs) /\
fnd_frame (rdW W mem1) /\
getr regs1 2 = w64 (spZ regs - 32) /\
getr regs1 3 = getr regs 3 /\
getr regs1 4 = getr regs 4 /\
getr regs1 19 = getr regs 19 /\
getr regs1 20 = getr regs 20 /\
getr regs1 21 = getr regs 21 /\
getr regs1 22 = getr regs 22 /\
getr regs1 23 = getr regs 23 /\
getr regs1 24 = getr regs 24 /\
getr regs1 25 = getr regs 25 /\
getr regs1 26 = getr regs 26 /\
getr regs1 27 = getr regs 27.
(* the loop head 0x89544 with k entries done, none of them named nm *)
Definition fnd_LHP (k : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
fnd_cut regs1 mem1 md1 /\ (k < length (rc_seg rcs))%nat /\
r_find rcs nm = r_find_go (skipn k (rc_seg rcs)) nm k /\
getr regs1 8 = w64 (c + 356 * Z.of_nat k) /\ getr regs1 9 = w64 name /\
getr regs1 18 = w64 (Z.of_nat (length (rc_seg rcs) - k)).

Lemma fnd_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
fnd_cut regs1 mem1 md1 ->
ajournal SEGS B FND_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
fnd_kept (rdW W mem1) (rdW W mem2) lo hi -> spZ regs - FND_STK <= lo -> hi <= spZ regs - 32 ->
getr regs2 2 = getr regs1 2 ->
(getr regs2 3 = getr regs1 3 /\
getr regs2 4 = getr regs1 4 /\
getr regs2 19 = getr regs1 19 /\
getr regs2 20 = getr regs1 20 /\
getr regs2 21 = getr regs1 21 /\
getr regs2 22 = getr regs1 22 /\
getr regs2 23 = getr regs1 23 /\
getr regs2 24 = getr regs1 24 /\
getr regs2 25 = getr regs1 25 /\
getr regs2 26 = getr regs1 26 /\
getr regs2 27 = getr regs1 27) ->
fnd_cut regs2 mem2 md2.
Proof using HPRE Hc64 Hnm64.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi (HJ & HK & HFR & R2 & RK) HJ2 HK2 Hlo Hhi Q2 QK.
pose proof fnd_sp as (Hal16 & Hlo2 & Hhi2 & Hslo & Hstk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FND_STK = 8224) by reflexivity.
split; [exact HJ2|]. split.
{ intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn). }
split.
{ intros j r Hr. assert (Hj : (j < 4)%nat)
    by (change 4%nat with (length fnd_saved); apply (proj1 (nth_error_Some fnd_saved j)); rewrite Hr; discriminate).
  apply (fnd_val_kept (rdW W mem1) _ lo hi);
    [exact HK2 | exact (HFR j r Hr) | lia | cbn [Z.of_nat]; lia | right; cbn [Z.of_nat]; lia]. }
destruct RK as (K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
destruct QK as (L3 & L4 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
split; [rewrite Q2; exact R2|].
repeat split; first [rewrite L3; exact K3 | rewrite L4; exact K4 | rewrite L19; exact K19 | rewrite L20; exact K20 | rewrite L21; exact K21 | rewrite L22; exact K22 | rewrite L23; exact K23 | rewrite L24; exact K24 | rewrite L25; exact K25 | rewrite L26; exact K26 | rewrite L27; exact K27].
Qed.

(* ---------- the epilogue: 0x8956c .. 0x89580, ra and s0-s2 restored, ret ---------- *)
Definition fnd_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) fnd_saved.
Lemma fnd_e_nth : forall j r, nth_error fnd_saved j = Some r ->
nth j fnd_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof using.
intros j r H. unfold fnd_e_extra. apply nth_error_nth.
rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j fnd_saved H). reflexivity.
Qed.
Lemma fnd_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 32) -> fnd_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 fnd_e_extra)) fnd_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FND_EPI)) mem1 (seg_rom SEGS)))
/\ YCbn.sh_ok SEGS fnd_Bx [] (Eimg (Ereg regs1 fnd_e_extra)) (mrestrict (w_H W) mem1).
Proof using HPRE Hc64 Hnm64.
intros regs1 mem1 R2 HFR. pose proof fnd_sp as (Hal16 & Hlo & Hhi & Hslo & Hstk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FND_STK = 8224) by reflexivity.
set (E := Eimg (Ereg regs1 fnd_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold fnd_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, fnd_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros cnk Hcnk. apply in_map_iff in Hcnk as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error fnd_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr.
  change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 32) (24 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
           (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, (fnd_e_nth j r Hr). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 32 + (24 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply fnd_val_mem_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok, fnd_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma fnd_epi : forall v regs1 mem1 md1, fnd_cut regs1 mem1 md1 -> getr regs1 10 = w64 v ->
v = seg_spec.find_ptr c rcs nm ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_EPI)) mem1 (seg_rom SEGS)) md1) fnd_Q.
Proof using HPRE Hc64 Hnm64.
intros v regs1 mem1 md1 (HJ & HK & HFR & R2 & RK) R10 Hv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fnd_sp as (Hal16 & Hlo & Hhi & Hslo & Hstkw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FND_STK = 8224) by reflexivity.
destruct (fnd_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 fnd_e_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs1 fnd_e_extra)) n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j r, nth_error fnd_saved j = Some r ->
  ew (Eimg (Ereg regs1 fnd_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 4)%nat)
    by (change 4%nat with (length fnd_saved); apply (proj1 (nth_error_Some fnd_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (fnd_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 fnd_e_extra)) 2) = spZ regs - 32)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33.
pose proof (EX 2%nat 9 eq_refl) as E34. pose proof (EX 3%nat 18 eq_refl) as E35.
cbn [Nat.add] in E32, E33, E34, E35.
pose proof (EE 3%nat 3%bv eq_refl) as Er3. pose proof (EE 4%nat 4%bv eq_refl) as Er4.
pose proof (EE 10%nat 10%bv eq_refl) as Er10.
pose proof (EE 19%nat 19%bv eq_refl) as Er19. pose proof (EE 20%nat 20%bv eq_refl) as Er20.
pose proof (EE 21%nat 21%bv eq_refl) as Er21. pose proof (EE 22%nat 22%bv eq_refl) as Er22.
pose proof (EE 23%nat 23%bv eq_refl) as Er23. pose proof (EE 24%nat 24%bv eq_refl) as Er24.
pose proof (EE 25%nat 25%bv eq_refl) as Er25. pose proof (EE 26%nat 26%bv eq_refl) as Er26.
pose proof (EE 27%nat 27%bv eq_refl) as Er27.
destruct RK as (Q3 & Q4 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
clear EX.
remember (Eimg (Ereg regs1 fnd_e_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_empty HFr KEEPe (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
pose proof (fnd_kept_trans _ _ _ _ _ _ _ HK KEEPe ltac:(lia) ltac:(lia)) as KEEP.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fnd_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 32 + 32) with (spZ regs) by lia;
    unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ exact E33 | exact E34 | exact E35
          | rewrite Er3, Q3; reflexivity | rewrite Er4, Q4; reflexivity
          | rewrite Er19, Q19; reflexivity | rewrite Er20, Q20; reflexivity
          | rewrite Er21, Q21; reflexivity | rewrite Er22, Q22; reflexivity
          | rewrite Er23, Q23; reflexivity | rewrite Er24, Q24; reflexivity
          | rewrite Er25, Q25; reflexivity | rewrite Er26, Q26; reflexivity
          | rewrite Er27, Q27; reflexivity ] ]. }
split; [rewrite F10, Er10, R10, Hv; reflexivity|].
split; [intros a Ha Hw _; apply KEEP; [exact Ha | exact Hw]|].
unfold sa_noalloc. split; [apply Permutation_refl|].
split; [reflexivity | exists (st_fs S); apply fnd_set_fs_self].
Qed.


(* ---------- the loop head 0x89544: the seed ---------- *)
Lemma fnd_LH_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 32) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) fnd_ss_LH
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)))
/\ YCbn.sh_ok SEGS fnd_Bx [] (Eimg (Ereg regs1 [])) (mrestrict (w_H W) mem1).
Proof using HPRE Hc64 Hnm64.
intros regs1 mem1 R2. pose proof fnd_sp as (Hal16 & Hlo & Hhi & Hslo & Hstkw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FND_STK = 8224) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 ([] : list word))) 2) = spZ regs - 32)
  by (rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold fnd_ss_LH. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok, fnd_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* ---------- the entry 0x894ec .. 0x89540 ---------- *)
Lemma fnd_stack_field : forall E H mem' cs off n v,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs) ->
bv_unsigned (ew E 2) = spZ regs ->
In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs -> ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof using Hc64 Hnm64.
intros E H mem' cs off n v HR Hsp Hin Hn Hv. apply fnd_sa_of_val_mem.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 (spZ regs) cs (-32) 0 (-32) 0 off 8 (SOff n 0) v HR Hsp Hin).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.
Definition fnd_x_extra : list word := map w64 [SB; Z.of_nat (length (rc_seg rcs))].
Lemma fnd_entry_seed :
st_ok_pi SEGS VAL (Eimg (Ereg regs fnd_x_extra)) fnd_ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_find)) mem (seg_rom SEGS)))
/\ YCbn.sh_ok SEGS fnd_Bx fnd_SH (Eimg (Ereg regs fnd_x_extra)) (mrestrict (w_H W) mem).
Proof using H10 H11 HPRE HQP Hc64 Hnm64 LAWS TL.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fnd_sp as (Hal16 & Hlo & Hhi & Hslo & Hstkw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof fnd_c_facts as (Hc4096 & Hcceil & Hc16 & Hcoff & Hcband).
pose proof fnd_n_le as HNle. assert (HST : FND_STK = 8224) by reflexivity.
pose proof fnd_name_facts as (Hn4096 & Hnceil).
set (E := Eimg (Ereg regs fnd_x_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; unfold fnd_x_extra; exact (fnd_ex_w64 regs [SB; Z.of_nat (length (rc_seg rcs))] 0
        ltac:(unfold A_TEXT; lia) ltac:(cbn; lia))).
assert (E33 : ew E 33 = w64 (Z.of_nat (length (rc_seg rcs))))
  by (subst E; unfold fnd_x_extra; exact (fnd_ex_w64 regs [SB; Z.of_nat (length (rc_seg rcs))] 1
        ltac:(unfold A_TEXT; lia) ltac:(cbn; lia))).
assert (U10 : bv_unsigned (ew E 10) = c)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64;
      apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = name)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64;
      apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SB)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = Z.of_nat (length (rc_seg rcs)))
  by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in HcellR, HgotR.
pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
destruct fnd_c_addr as (CA0 & CA1 & CA2 & CA3 & CA4).
split.
- rewrite restrict_mkst_fx. unfold fnd_ss_entry. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, fnd_nreg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia);
         reflexivity | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 11392 4 (SOff 33 0) (Z.of_nat (length (rc_seg rcs))));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
      apply fnd_val_mem_of_sa. replace (c + 11392) with (c + seg_spec.RC_N) by (unfold seg_spec.RC_N; lia).
      exact fnd_n_val.
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, fnd_nreg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img in Hcoff.
    destruct Hcoff as [Hco | Hco]; repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok].
    unfold afact_ok, fnd_spF, fnd_SBF, fnd_NF, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, U32, U33, U10, U11. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; try exact Hal16; unfold SB; lia.
- unfold YCbn.sh_ok, fnd_SH. apply Forall_cons; [|apply Forall_nil].
  apply (fnd_shent_ok E _ 10 c 0 16616 E32 U10); try lia.
  + rewrite Z.add_0_r. replace (16616 - 0) with 16616 by lia. unfold SB. exact CA3.
  + intros y Hy. apply Hcband. lia.
Qed.

Lemma fnd_entry :
  (forall k regs1 mem1 md1, fnd_LHP k regs1 mem1 md1 ->
     SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)) md1) fnd_Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_segconf_find) regs mem md) fnd_Q.
Proof using H10 H11 HPRE HQP Hc64 Hnm64 TL.
intros LOOP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof fnd_sp as (Hal16 & Hlo & Hhi & Hslo & Hstkw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : FND_STK = 8224) by reflexivity.
pose proof fnd_c_facts as (Hc4096 & Hcceil & Hc16 & Hcoff & Hcband).
pose proof fnd_n_le as HNle.
destruct fnd_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B FND_STK [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs fnd_x_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs fnd_x_extra)) n = getr regs r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (Eimg (Ereg regs fnd_x_extra)) 33 = w64 (Z.of_nat (length (rc_seg rcs))))
  by (unfold fnd_x_extra; exact (fnd_ex_w64 regs [SB; Z.of_nat (length (rc_seg rcs))] 1
        ltac:(unfold A_TEXT; lia) ltac:(cbn; lia))).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs fnd_x_extra)) 2) = spZ regs)
  by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
remember (Eimg (Ereg regs fnd_x_extra)) as E eqn:HE. clear HE.
assert (FRM : forall H mem' cs,
  region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs) ->
  (forall j r, nth_error fnd_saved j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  fnd_frame (aview SEGS H mem')).
{ intros H mem' cs HR Hin j r Hr.
  assert (Hr' : 1 <= r <= 18) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (fnd_stack_field E H mem' cs _ (Z.to_nat r)); [exact HR | exact Usp | exact (Hin j r Hr) | |
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr;
    change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
  rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_find)) with (Z_to_bv 64 (BASE + AF_reac_segconf_find)).
(* 0x894ec .. 0x89540: the frame, the NULL tests, the checked load of c->n, blez s2 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_win HFr KEEP0 (spZ regs - FND_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <= 0: no entry, a0 = 0 *)
  assert (H0 : length (rc_seg rcs) = 0%nat).
  { rewrite (fnd_bge0 E 33 (Z.of_nat (length (rc_seg rcs))) E33) in Hc by lia.
    apply Z.leb_le in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FND_EPI.
  { awr_ok_tac; exact Usp. }
  fnd_md.
  fnd_keep_win HFr KEEP1 (spZ regs - FND_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) F2. prreg HS (10%bv : bv 5) F10.
  apply (fnd_epi 0).
  + split; [exact HJ|]. split; [apply (fnd_kept_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia|].
    split.
    { apply (FRM _ _ _ HRg). intros j r Hr.
      do 4 (destruct j as [|j];
        [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr. }
    split; [rewrite F2, Usp; reflexivity|].
    repeat split;
      (rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
       lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
         let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
       cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity).
  + exact F10.
  + unfold seg_spec.find_ptr. destruct (r_find rcs nm) as [i|] eqn:Ef; [|reflexivity].
    exfalso. apply seg_query_facts.sq_find_lt in Ef. lia.
- (* n > 0: the loop, with k = 0 *)
  assert (H0 : (0 < length (rc_seg rcs))%nat).
  { rewrite (fnd_bge0 E 33 (Z.of_nat (length (rc_seg rcs))) E33) in Hc by lia.
    apply Z.leb_gt in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FND_LH.
  { awr_ok_tac; exact Usp. }
  fnd_md.
  fnd_keep_win HFr KEEP1 (spZ regs - FND_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) F2. prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9.
  prreg HS (18%bv : bv 5) F18.
  apply (LOOP 0%nat).
  split; [split; [exact HJ|]|].
  + split; [apply (fnd_kept_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia|].
    split.
    { apply (FRM _ _ _ HRg). intros j r Hr.
      do 4 (destruct j as [|j];
        [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr. }
    split; [rewrite F2, Usp; reflexivity|].
    repeat split;
      (rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
       lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
         let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
       cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity).
  + split; [exact H0|]. split; [reflexivity|].
    split; [rewrite F8, (EE 10%nat 10%bv eq_refl), H10; unfold w64; f_equal; lia|].
    split; [rewrite F9, (EE 11%nat 11%bv eq_refl), H11; reflexivity|].
    rewrite F18, E33. unfold w64. f_equal. lia.
Qed.

End w.
End e.
End d.
End b.
