(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v, with its module paths and module names changed; 2273 of its 2322 lines of code are new or changed and 374 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aOpen.v, with its module paths, module names and numbers changed; 968 of its 1085 lines of code are new or changed and 2205 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, 1be0f53d / bff8519b): the SHARED WHITESPACE LOOP of ex_value.
   Three of the five inlined ex_ws loops (fuzz_preset.c :103-107) have equal words except their two report targets:
   at A' 0x838a4 (piece 7, before an object's key), 0x839c0 (piece 7, before ':') and 0x83a7c (piece 8, after an
   item); their exits are 0x838f0, 0x83a0c, 0x83ac8. ws_loop_raw walks any of them: from the loop's first slot with
   a0 = a2 = in->p = x0 + i < in->end = a1, to its exit with in->p (and a0, a2) at the first non-blank byte or at the
   end; every blank stored back to in->p (8 bytes at q, the only write). Its frame is the engine's RAW one: every word
   off [q, q + 8) of the restricted memory mrestrict (w_H W) mem is unchanged (chained from each run's frame_of), and
   the restricted memory grows (each run's mem_grows).
   ev_ws_loop (Section v) is S8aIface.v's ev_ws_loop_spec at image A (PI := prh_img_A, L := A_prog_listing,
   PA := PI_prog_A), raw-frame conjunct included: ws_loop_raw from ev_pre / ev_mid / ev_regs, and ev_mid carried to
   the new cursor by ws_mid_keep (every byte ev_mid reads outside the caller window lies below q; the tree's
   footprint misses [q, q + 40) by ev_pre). Section hypothesis: LAWS (AR_laws_x at any head length) only.
   MEMNORM (ev_mid's last conjunct, S8aIface.v): ws_loop_raw keeps `YAkMemnorm.memnorm SEGS mem` across every runner
   segment by YC1fPx's `*_inv` runners (paj_run_x_inv / paj_run_to_x_inv and their tactics) at P := that predicate,
   laws YSRrMemnorm.srr_inv_laws_memnorm_k; ev_ws_loop hands it to ws_mid_keep at the exit memory.
   Numerals: offsets 0x600 / 0x64c, 0x71c / 0x768, 0x7d8 / 0x824 (LENGTH: pc - 0x832a4 on the bff8519b listing);
   7364 (LENGTH: ex_value's listing offset); atom indices 32, 33 (DERIVED: Ereg's extra atoms); 8, 1 (LENGTH: access
   sizes); 32, 255, 256 (WORD / LENGTH: the blank bound, byte range); 4096 (LENGTH: the low page every block is
   above); 40, 56, 128, 152, 248, 256, 288 (LENGTH: struct ex, a pj_value node, the class-1 fake frame, EV_SAVED's
   lowest and highest offset, the save area, the save area plus one 32-alignment); 2 ^ 41, 2 ^ 42, 2 ^ 44, 2 ^ 46,
   2 ^ 47, 2 ^ 64 (DERIVED: shadow, stack and word bounds); 2147450880 (DERIVED: SHADOW_OFF, unfolded). No ADDRESS:
   the statics' addresses are prh_img_A's fields (PRH_Img.v), read by computation. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YN0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the three loops (S8aIface.EV_WSLOOPS) and the blank mask (S8aIface.EV_WSMASK) are the interface's *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS; hl, since HL clashes with proof names *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

#[local] Notation RUN := (@paj_run_x fx rc SK A_prog_listing PL_prog_A PA B PST ARx hl LAWS).
#[local] Notation RUNTO := (@paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B PST ARx hl LAWS).
#[local] Notation BR := (paj_branch (PI := PA)).
(* the memnorm-keeping runners: YC1fPx's _inv twins at P := YAkMemnorm.memnorm SEGS *)
#[local] Notation MN := (YAkMemnorm.memnorm SEGS).
#[local] Notation RUNI := (@paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx hl LAWS MN
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
#[local] Notation RUNTOI := (@paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx hl LAWS MN
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).

Lemma ev_sigma_val : SIGMA AS_ex_value = BASE + 7364.
Proof. vm_compute. reflexivity. Qed.

(* the symbolic state at a loop's first slot b (listing offset 7364 + b): a0 = a2 = p (atom 12), the text byte at p
   (atom 32, a one-byte read-only region at a2), in->p at s3 (an 8-byte writable region), the shadow byte of q at s10
   (a one-byte read-only region holding 0), s11 = 32, s6 = the mask; the shadow base s8 is the token base. *)
Definition WS_Bx : sv := SOff 24 0.
Definition WS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ws_regions : smem :=
  [ YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 12 0))];
    YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ].
Definition ws_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 12 0)) 27%bv (SLit 32)) 22%bv (SLit EV_WSMASK).
Definition ws_facts : facts :=
  mkFacts [ (12%nat, mkAF 4096 (2 ^ 47 - 1) 0); (11%nat, mkAF 4096 (2 ^ 47) 0); (19%nat, mkAF (2 ^ 46) (2 ^ 47) 3);
            (26%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 0 255 0) ] [] [].
Definition ss_ws (b : Z) : sstate := mkSS (7364 + b) ws_regs ws_regions None ws_facts.
Definition ws_SH : list shent := [mkSHE 12 0 1].



(* the 8 bytes a CVal 8 chunk denotes, as val_mem *)
Lemma ws_val_mem_of_chunk : forall E (m : word -> option byte) base e v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m base 8 v.
Proof.
intros E m base e v Hc He Hv k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (bb & Hb & Hm).
cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
replace (base + 0 + Z.of_nat k) with (base + Z.of_nat k) in Hm by lia. rewrite Hm. f_equal.
injection Hb as <-. unfold byte_of_word, YO0f.le_byte. rewrite He, unsigned_lit_small by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small with (a := v) by (change (8 * Z.of_nat 8) with 64; lia).
rewrite Z.mod_mod by lia. reflexivity.
Qed.


(* the write premise of every stretch: the one window is in->p's 8 bytes at s3, inside the caller's window *)
Ltac ws_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch goal with E19 : ew ?E0 19 = Z_to_bv 64 ?q |- _ =>
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat q);
    [reflexivity | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); rewrite ?E19; apply unsigned_lit_small; lia
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; lia |] end;
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

(* the write set of every stretch is in->p's 8 bytes: an address outside them is not in a region's window *)
Ltac ws_notin :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]);
  try destruct Hin;
  repeat match goal with E19 : ew ?E0 19 = Z_to_bv 64 ?qq, Hr : context [ew ?E1 19] |- _ =>
    cbn [ew ewset Nat.eqb extK] in Hr; rewrite ?ew_havoc_old in Hr by (cbv; lia); rewrite ?E19 in Hr;
    rewrite unsigned_lit_small in Hr by lia; lia end.
(* turn a run's frame_of into the raw frame from the loop's entry memory, chaining the previous one (KM), and its
   mem_grows into growth from the entry memory (KG) *)
Ltac ws_keep q mem0 KM KG K G :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?mA) (mrestrict _ ?mB), HG : mem_grows (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
    assert (K : forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict Hh mB y = mrestrict Hh mem0 y) by
      (let y := fresh "y" in let Hn := fresh "Hn" in
       intros y Hn; rewrite (HFr y); [exact (KM y Hn) | ws_notin]);
    assert (G : mem_grows (mrestrict Hh mem0) (mrestrict Hh mB)) by exact (mem_grows_trans _ _ _ KG HG);
    clear HFr HG KM KG
  end.

(* the registers the loop does not write: every one but a0, a2, a3, a4 *)
Definition WS_KEPT : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv.
Lemma ws_reg_cases : forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
  r = 0%bv \/ r = 22%bv \/ r = 27%bv \/ In r WS_KEPT.
Proof.
intros r H10 H12 H13 H14. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [contradiction | left; reflexivity | right; left; reflexivity
  | right; right; left; reflexivity | right; right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma ws_ws_big : forall b, 32 < b -> PjGrammar.ws b = false.
Proof. intros b Hb. unfold PjGrammar.ws. repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

(* the exit: the state at the exit pc, its registers, the in->p chunk, the raw frame off in->p, the growth *)
Ltac ws_fin ip :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ssc (restrict (w_H ?Wx) ?msx),
    KM : forall y : word, ~ (?qq <= bv_unsigned y < ?qq + 8) -> _ = _, KG : mem_grows _ _,
    HAE : env_agree 32 (Ereg ?regs0 ?extra) _, E12 : ew _ 12 = Z_to_bv 64 ?pp, E19 : ew _ 19 = Z_to_bv 64 ?qq2 |- _ =>
    let HSt := fresh "HSt" in pose proof HS as HSt; unfold st_ok_pi in HSt;
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs0 extra WS_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    let R10 := fresh "R10" in let R12 := fresh "R12" in let R22 := fresh "R22" in let R27 := fresh "R27" in
    prreg HS (10%bv : bv 5) R10; prreg HS (12%bv : bv 5) R12; prreg HS (22%bv : bv 5) R22; prreg HS (27%bv : bv 5) R27;
    pmkst HS; apply SRr_ret; split; [reflexivity|];
    lazymatch goal with |- exists _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d, ip end;
    split; [reflexivity|];
    split; [eassumption|];
    split; [eassumption|];
    split; [exact KM|];
    split; [exact KG|];
    split; [idtac|];
    [ idtac | split; [lia|]; split; [idtac|]; [idtac | split; [idtac|]; [idtac | split; [idtac|]]] ]
  end.

(* in->p's 8 bytes from the region-19 chunk of the state (its value the symbolic sv) *)
Ltac ws_vq sv :=
  lazymatch goal with HSt : st_ok _ ?Ec _ (restrict _ ?msx), E19 : ew _ 19 = Z_to_bv 64 ?qq |- val_mem _ _ ?qq 8 _ =>
    let HC := fresh "HC" in
    pose proof (st_ok_chunk SEGS _ _ _ 1%nat (YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 sv)])
      (YP09.mkChunk 0 (CVal 8 sv)) HSt ltac:(vm_compute; reflexivity) ltac:(left; reflexivity)) as HC;
    cbn [ms_mem restrict base_val YP09.r_base] in HC;
    cbn [ew ewset Nat.eqb extK] in HC; rewrite ?ew_havoc_old in HC by (cbv; lia); rewrite E19, unsigned_lit_small in HC by lia;
    eapply (ws_val_mem_of_chunk _ _ _ sv _ HC); [|lia]
  end.
Ltac ws_den :=
  cbn [sv_denot ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia);
  repeat match goal with E12 : ew _ 12 = Z_to_bv 64 _ |- context [ew _ 12] => rewrite E12 end;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; try reflexivity.
Ltac ws_regs_kept :=
  let r := fresh "r" in let h10 := fresh in let h12 := fresh in let h13 := fresh in let h14 := fresh in
  intros r h10 h12 h13 h14; destruct (ws_reg_cases r h10 h12 h13 h14) as [->|[->|[->|Hin]]];
  [ rewrite !getr_zero; reflexivity
  | match goal with R22 : getr _ 22 = _, H22 : getr _ 22 = _ |- _ => rewrite R22, H22; reflexivity end
  | match goal with R27 : getr _ 27 = _, H27 : getr _ 27 = _ |- _ => rewrite R27, H27; reflexivity end
  | match goal with HK : forall r, In r WS_KEPT -> _ |- _ => exact (HK _ Hin) end ].

Lemma ws_mask_bit : forall bi, 0 <= bi <= 32 ->
  (zcanon (Z.land (zcanon (Z.shiftr (zcanon 4294977024) (Z.land bi 63))) (zcanon 1)) =? zcanon 0) = negb (PjGrammar.ws bi).
Proof.
intros bi Hb.
assert (H : forallb (fun k => Bool.eqb ((zcanon (Z.land (zcanon (Z.shiftr (zcanon 4294977024) (Z.land (Z.of_nat k) 63)))
  (zcanon 1)) =? zcanon 0)) (negb (PjGrammar.ws (Z.of_nat k)))) (seq 0 33) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H.
specialize (H (Z.to_nat bi) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Bool.eqb_prop in H. exact H.
Qed.

(* bytes and shadow facts read through aview survive a write that misses them *)
Lemma ws_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview SEGS H m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v HK Hv k Hk. specialize (HK k Hk). specialize (Hv k Hk). unfold aview in HK.
rewrite Hv in HK. destruct (mbyte SEGS (mrestrict H m') (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate HK].
cbn [option_map] in HK. injection HK as HK. f_equal. apply bv_eq. rewrite HK. reflexivity.
Qed.
Lemma ws_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) x0 x,
  (forall a, x0 <= a < x0 + Z.of_nat (length x) -> aview SEGS H m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) x0 x -> garr8 SEGS (mrestrict H m') x0 x.
Proof.
intros H m m' x0 x HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (ws_val_mem_keep H m m'); [|exact Hv]. intros k Hk. apply HK. lia.
Qed.
Lemma ws_writable_of_st_ok : forall E ss (ms : machine_state) r o,
  st_ok SEGS E ss ms -> In r (ss_mem ss) -> YP09.r_wlo r <= o < YP09.r_whi r ->
  writable_at SEGS (ms_mem ms) (base_val E (YP09.r_base r) + o).
Proof.
intros E ss ms r o HS Hin Ho. pose proof (st_ok_mem_ok SEGS E ss ms HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR r Hin) as (_ & _ & Hw & _). exact (Hw o Ho).
Qed.

Lemma ws_sh_out : forall sh q, SHADOW_OFF <= sh < kHighMemBeg -> 2 ^ 46 <= q -> 0 <= sh < 2 ^ 64 /\ ~ (q <= sh < q + 8).
Proof. intros sh q H1 H2. unfold SHADOW_OFF, kHighMemBeg in H1. lia. Qed.

(* the raw frame read through the view: a byte of the word range off [q, q + 8) reads the same *)
Lemma ws_av_raw : forall (H : word -> bool) (m m' : word -> option byte) q,
  (forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict H m' y = mrestrict H m y) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' q K a Ha Hn. unfold aview, mbyte. rewrite (K (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma ws_loop_raw : forall b e, In (b, e) EV_WSLOOPS ->
  forall (k : nat) W (regs : bvmap 5 word) mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk
    (q x0 : Z) (x : list Z) (i : nat),
  k = (length x - i)%nat -> (i < length x)%nat ->
  ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  sp0 - STK <= q -> q + 8 <= sp0 -> 2 ^ 46 <= q -> q + 8 <= 2 ^ 47 -> q mod 8 = 0 ->
  4096 <= x0 -> amem_range x0 (Z.of_nat (length x)) -> x0 + Z.of_nat (length x) <= 2 ^ 47 ->
  (x0 + Z.of_nat (length x) <= q \/ q + 8 <= x0) ->
  getr regs 10 = w64 (x0 + Z.of_nat i) -> getr regs 12 = w64 (x0 + Z.of_nat i) ->
  getr regs 11 = w64 (x0 + Z.of_nat (length x)) ->
  getr regs 19 = w64 q -> getr regs 24 = w64 SHADOW_OFF -> getr regs 26 = w64 (shadow_addr q) ->
  getr regs 27 = w64 32 -> getr regs 22 = w64 EV_WSMASK ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 (x0 + Z.of_nat i) ->
  garr8 SEGS (mrestrict (w_H W) mem) x0 x ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x0 (Z.of_nat (length x)) ->
  aview SEGS (w_H W) mem (shadow_addr q) = Some 0 ->
  (forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (q + o)) ->
  YAkMemnorm.memnorm SEGS mem ->
  SRr SEGS W (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (7364 + b))) mem (YK11.seg_rom SEGS)) md)
    (fun W' c' => W' = W /\ exists regs' mem' md' (i' : nat),
       c' = mkCfg (YK11.mkst regs' (Z_to_bv 64 (BASE + (7364 + e))) mem' (YK11.seg_rom SEGS)) md' /\
       ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
       YAkMemnorm.memnorm SEGS mem' /\
       (forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict (w_H W) mem' y = mrestrict (w_H W) mem y) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
       val_mem SEGS (mrestrict (w_H W) mem') q 8 (x0 + Z.of_nat i') /\
       (i <= i' <= length x)%nat /\ skipn i' x = PjGrammar.skip (skipn i x) /\
       getr regs' 10 = w64 (x0 + Z.of_nat i') /\ getr regs' 12 = w64 (x0 + Z.of_nat i') /\
       (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r)).
Proof.
intros b e Hbe.
destruct Hbe as [Hbe|[Hbe|[Hbe|[]]]]; injection Hbe as <- <-.
{ (* loop at 0x600, exit 0x64c *)
induction k as [|k IH]; intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x i
  Hk Hi HJ Hq1 Hq2 Hq3 Hq4 Hq8 Hx1 Ham Hx2 Hxq H10 H12 H11 H19 H24 H26 H27 H22 Hvq Hgx Hrax Hshq Hwq HMN; [lia|].
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (len := Z.of_nat (length x)) in *.
set (p := x0 + Z.of_nat i) in *.
set (bi := nth i x 0) in *.
destruct (Hgx i Hi) as [Hvb Hbi].
remember (Eimg (Ereg regs [Z_to_bv 64 bi])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 bi]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 EV_WSMASK) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 32) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 bi) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 bi]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (Hsq : SHADOW_OFF <= shadow_addr q < kHighMemBeg)
  by (unfold shadow_addr, SHADOW_OFF, kHighMemBeg; pose proof (Z.div_pos q 8); assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia).
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + (7364 + ?bb))) _ _) _) _ => set (b := bb) end.
assert (HS : st_ok_pi SEGS VAL E (ss_ws b)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (7364 + b))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ws. apply pa_entry_st_ok_full.
  - unfold ws_regs. rewrite HE.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | |] | |] | |];
      try (intros X; discriminate X); cbn [sv_denot]; rewrite <- ?HE.
    + rewrite H10, E12, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + exact H27.
    + exact H22.
  - vm_compute. reflexivity.
  - unfold ws_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 12%nat p E12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) bi); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvb.
    + rewrite (VB 19%nat q E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hwq o Ho)|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 12 0) p); [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvq.
    + assert (Hsq2 : 0 <= shadow_addr q < 2 ^ 47) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
      rewrite (VB 26%nat (shadow_addr q) E26) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      intros kk0 Hkk0. replace kk0 with 0%nat by lia. rewrite !Z.add_0_r.
      unfold aview in Hshq. destruct (mbyte SEGS (mrestrict (w_H W) mem) (shadow_addr q)) as [bb|] eqn:Hbb;
        [|discriminate Hshq]. cbn [option_map] in Hshq. injection Hshq as Hb0. f_equal. apply bv_eq.
      rewrite Hb0. reflexivity.
  - apply pairwise_disjoint_of_extents. unfold ws_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 12%nat p E12) by lia. rewrite (VB 19%nat q E19) by lia.
    rewrite (VB 26%nat (shadow_addr q) E26) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in Ham. unfold kHighMemBeg, SHADOW_OFF in Hsq.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ws_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E11, E19, E26, E24, E32, !unsigned_lit_small
      by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold kHighMemBeg, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS WS_Bx ws_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ws_SH. constructor; [|constructor].
  assert (UBx : U E WS_Bx = SHADOW_OFF) by (unfold WS_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
  assert (Up : U E (SOff 12 0) = p) by (apply (U_atom E 12 p E12); lia).
  unfold shent_ok. cbn [she_m she_lo she_hi]. split.
  - rewrite UBx, Up. intros a Ha. apply (Hrax a). lia.
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite Up in Ha. rewrite UBx.
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof RUN as RUNh. pose proof RUNTO as RUNTOh. pose proof BR as BRh.
pose proof RUNI as RUNIh. pose proof RUNTOI as RUNTOIh.
assert (KM0 : forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict (w_H W) mem y = mrestrict (w_H W) mem y)
  by (intros; reflexivity).
assert (KG0 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
{ ws_awr. }
clear HF. ws_keep q mem KM0 KG0 KM1 KG1.
psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
- (* 32 < byte: not a blank; the branch goes to the exit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x64c).
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  ws_fin i.
  + ws_vq (SOff 12 0). ws_den.
  + rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite (ws_ws_big bi Hc). reflexivity.
  + rewrite R10. ws_den.
  + rewrite R12. ws_den.
  + ws_regs_kept.
- (* byte <= 32: test the mask bit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_true_iff in Hc0.
    paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x64c).
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    ws_fin i.
    * ws_vq (SOff 12 0). ws_den.
    * rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite Hc0. reflexivity.
    * rewrite R10. ws_den.
    * rewrite R12. ws_den.
    * ws_regs_kept.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_false_iff in Hc0.
    paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
    * (* p + 1 <> end: back to the loop's first slot, then the loop's remaining iterations (IH) *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_true_iff, Z.eqb_neq in Hc1.
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x600).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      pose proof HS as HSt. unfold st_ok_pi in HSt.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs [Z_to_bv 64 bi] WS_KEPT HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) R10. prreg HS (12%bv : bv 5) R12. prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      assert (Hvq1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat (Nat.succ i))).
      { ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity. }
      assert (Hw1 : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms)) (q + o)).
      { intros o Ho.
        pose proof (ws_writable_of_st_ok _ _ _ (YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 12 1))]) o
          HSt ltac:(vm_compute; right; left; reflexivity) ltac:(cbn; lia)) as Hw.
        cbn [ms_mem restrict base_val YP09.r_base] in Hw. cbn [ew ewset Nat.eqb extK] in Hw.
        rewrite ?ew_havoc_old in Hw by (cbv; lia). rewrite E19, unsigned_lit_small in Hw by lia. exact Hw. }
      assert (Hsh : forall a, x0 <= a < x0 + len -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF a < kHighMemBeg).
      { intros a Ha. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *. pose proof (Z.div_pos a 8).
        assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
      pmkst HS.
      eapply SRr_mono.
      { eapply (IH W (ms_regs ms) (ms_mem ms) _ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x (Nat.succ i));
          try eassumption; try lia.
        all: lazymatch goal with
          | |- getr _ 10 = _ => rewrite R10; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 12 = _ => rewrite R12; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 27 = _ => rewrite R27; exact H27
          | |- getr _ 22 = _ => rewrite R22; exact H22
          | |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption
          | |- garr8 _ _ _ _ => apply (ws_garr8_keep _ mem); [|exact Hgx]; intros a Ha; apply (ws_av_raw _ _ _ q KM4); lia
          | |- range_addressable _ _ _ _ =>
              intros a Ha; destruct (Hrax a Ha) as (sv & Hsv & Hok); exists sv; split; [|exact Hok];
              destruct (ws_sh_out _ q (Hsh a Ha) Hq3) as [Hs1 Hs2];
              rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hsv
          | |- aview _ _ _ (shadow_addr _) = _ =>
              destruct (ws_sh_out _ q Hsq Hq3) as [Hs1 Hs2]; rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hshq
          | |- ?g => idtac "WSG_IHleft" g; fail
          end. }
      cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & i2 & -> & HJ2 & HMN2 & KM5 & KG5 & Hvq2 & Hii & Hsk & H102 & H122 & HK2).
      split; [reflexivity|]. exists regs2, mem2, md2, i2.
      split; [reflexivity|]. split; [exact HJ2|]. split; [exact HMN2|].
      split; [intros y Hn; rewrite (KM5 y Hn); exact (KM4 y Hn)|].
      split; [exact (mem_grows_trans _ _ _ KG4 KG5)|].
      split; [exact Hvq2|]. split; [lia|].
      split; [rewrite Hsk, (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite Hc0; reflexivity|].
      split; [exact H102|]. split; [exact H122|].
      intros r h1 h2 h3 h4. rewrite (HK2 r h1 h2 h3 h4). revert r h1 h2 h3 h4. ws_regs_kept.
    * (* p + 1 = end: `j exit` *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_false_iff, Z.eqb_eq in Hc1.
      assert (Hend : Nat.succ i = length x).
      { assert (Hc1' : x0 + Z.of_nat i + 1 = x0 + Z.of_nat (length x)) by exact Hc1.
        apply Nat2Z.inj. rewrite Nat2Z.inj_succ. unfold Z.succ. apply (Z.add_cancel_l _ _ x0). rewrite Z.add_assoc. exact Hc1'. }
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x64c).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      ws_fin (Nat.succ i).
      -- ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- assert (Hz : skipn (Datatypes.S i) x = []) by (apply skipn_all2; rewrite <- Hend; constructor).
         change (Nat.succ i) with (Datatypes.S i). rewrite (skipn_nth x i 0 Hi), Hz. cbn [PjGrammar.skip]. fold bi. rewrite Hc0.
         reflexivity.
      -- rewrite R10. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- rewrite R12. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- ws_regs_kept.
}
{ (* loop at 0x71c, exit 0x768 *)
induction k as [|k IH]; intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x i
  Hk Hi HJ Hq1 Hq2 Hq3 Hq4 Hq8 Hx1 Ham Hx2 Hxq H10 H12 H11 H19 H24 H26 H27 H22 Hvq Hgx Hrax Hshq Hwq HMN; [lia|].
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (len := Z.of_nat (length x)) in *.
set (p := x0 + Z.of_nat i) in *.
set (bi := nth i x 0) in *.
destruct (Hgx i Hi) as [Hvb Hbi].
remember (Eimg (Ereg regs [Z_to_bv 64 bi])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 bi]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 EV_WSMASK) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 32) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 bi) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 bi]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (Hsq : SHADOW_OFF <= shadow_addr q < kHighMemBeg)
  by (unfold shadow_addr, SHADOW_OFF, kHighMemBeg; pose proof (Z.div_pos q 8); assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia).
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + (7364 + ?bb))) _ _) _) _ => set (b := bb) end.
assert (HS : st_ok_pi SEGS VAL E (ss_ws b)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (7364 + b))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ws. apply pa_entry_st_ok_full.
  - unfold ws_regs. rewrite HE.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | |] | |] | |];
      try (intros X; discriminate X); cbn [sv_denot]; rewrite <- ?HE.
    + rewrite H10, E12, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + exact H27.
    + exact H22.
  - vm_compute. reflexivity.
  - unfold ws_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 12%nat p E12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) bi); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvb.
    + rewrite (VB 19%nat q E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hwq o Ho)|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 12 0) p); [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvq.
    + assert (Hsq2 : 0 <= shadow_addr q < 2 ^ 47) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
      rewrite (VB 26%nat (shadow_addr q) E26) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      intros kk0 Hkk0. replace kk0 with 0%nat by lia. rewrite !Z.add_0_r.
      unfold aview in Hshq. destruct (mbyte SEGS (mrestrict (w_H W) mem) (shadow_addr q)) as [bb|] eqn:Hbb;
        [|discriminate Hshq]. cbn [option_map] in Hshq. injection Hshq as Hb0. f_equal. apply bv_eq.
      rewrite Hb0. reflexivity.
  - apply pairwise_disjoint_of_extents. unfold ws_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 12%nat p E12) by lia. rewrite (VB 19%nat q E19) by lia.
    rewrite (VB 26%nat (shadow_addr q) E26) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in Ham. unfold kHighMemBeg, SHADOW_OFF in Hsq.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ws_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E11, E19, E26, E24, E32, !unsigned_lit_small
      by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold kHighMemBeg, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS WS_Bx ws_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ws_SH. constructor; [|constructor].
  assert (UBx : U E WS_Bx = SHADOW_OFF) by (unfold WS_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
  assert (Up : U E (SOff 12 0) = p) by (apply (U_atom E 12 p E12); lia).
  unfold shent_ok. cbn [she_m she_lo she_hi]. split.
  - rewrite UBx, Up. intros a Ha. apply (Hrax a). lia.
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite Up in Ha. rewrite UBx.
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof RUN as RUNh. pose proof RUNTO as RUNTOh. pose proof BR as BRh.
pose proof RUNI as RUNIh. pose proof RUNTOI as RUNTOIh.
assert (KM0 : forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict (w_H W) mem y = mrestrict (w_H W) mem y)
  by (intros; reflexivity).
assert (KG0 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
{ ws_awr. }
clear HF. ws_keep q mem KM0 KG0 KM1 KG1.
psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
- (* 32 < byte: not a blank; the branch goes to the exit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x768).
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  ws_fin i.
  + ws_vq (SOff 12 0). ws_den.
  + rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite (ws_ws_big bi Hc). reflexivity.
  + rewrite R10. ws_den.
  + rewrite R12. ws_den.
  + ws_regs_kept.
- (* byte <= 32: test the mask bit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_true_iff in Hc0.
    paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x768).
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    ws_fin i.
    * ws_vq (SOff 12 0). ws_den.
    * rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite Hc0. reflexivity.
    * rewrite R10. ws_den.
    * rewrite R12. ws_den.
    * ws_regs_kept.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_false_iff in Hc0.
    paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
    * (* p + 1 <> end: back to the loop's first slot, then the loop's remaining iterations (IH) *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_true_iff, Z.eqb_neq in Hc1.
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x71c).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      pose proof HS as HSt. unfold st_ok_pi in HSt.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs [Z_to_bv 64 bi] WS_KEPT HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) R10. prreg HS (12%bv : bv 5) R12. prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      assert (Hvq1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat (Nat.succ i))).
      { ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity. }
      assert (Hw1 : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms)) (q + o)).
      { intros o Ho.
        pose proof (ws_writable_of_st_ok _ _ _ (YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 12 1))]) o
          HSt ltac:(vm_compute; right; left; reflexivity) ltac:(cbn; lia)) as Hw.
        cbn [ms_mem restrict base_val YP09.r_base] in Hw. cbn [ew ewset Nat.eqb extK] in Hw.
        rewrite ?ew_havoc_old in Hw by (cbv; lia). rewrite E19, unsigned_lit_small in Hw by lia. exact Hw. }
      assert (Hsh : forall a, x0 <= a < x0 + len -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF a < kHighMemBeg).
      { intros a Ha. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *. pose proof (Z.div_pos a 8).
        assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
      pmkst HS.
      eapply SRr_mono.
      { eapply (IH W (ms_regs ms) (ms_mem ms) _ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x (Nat.succ i));
          try eassumption; try lia.
        all: lazymatch goal with
          | |- getr _ 10 = _ => rewrite R10; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 12 = _ => rewrite R12; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 27 = _ => rewrite R27; exact H27
          | |- getr _ 22 = _ => rewrite R22; exact H22
          | |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption
          | |- garr8 _ _ _ _ => apply (ws_garr8_keep _ mem); [|exact Hgx]; intros a Ha; apply (ws_av_raw _ _ _ q KM4); lia
          | |- range_addressable _ _ _ _ =>
              intros a Ha; destruct (Hrax a Ha) as (sv & Hsv & Hok); exists sv; split; [|exact Hok];
              destruct (ws_sh_out _ q (Hsh a Ha) Hq3) as [Hs1 Hs2];
              rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hsv
          | |- aview _ _ _ (shadow_addr _) = _ =>
              destruct (ws_sh_out _ q Hsq Hq3) as [Hs1 Hs2]; rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hshq
          | |- ?g => idtac "WSG_IHleft" g; fail
          end. }
      cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & i2 & -> & HJ2 & HMN2 & KM5 & KG5 & Hvq2 & Hii & Hsk & H102 & H122 & HK2).
      split; [reflexivity|]. exists regs2, mem2, md2, i2.
      split; [reflexivity|]. split; [exact HJ2|]. split; [exact HMN2|].
      split; [intros y Hn; rewrite (KM5 y Hn); exact (KM4 y Hn)|].
      split; [exact (mem_grows_trans _ _ _ KG4 KG5)|].
      split; [exact Hvq2|]. split; [lia|].
      split; [rewrite Hsk, (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite Hc0; reflexivity|].
      split; [exact H102|]. split; [exact H122|].
      intros r h1 h2 h3 h4. rewrite (HK2 r h1 h2 h3 h4). revert r h1 h2 h3 h4. ws_regs_kept.
    * (* p + 1 = end: `j exit` *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_false_iff, Z.eqb_eq in Hc1.
      assert (Hend : Nat.succ i = length x).
      { assert (Hc1' : x0 + Z.of_nat i + 1 = x0 + Z.of_nat (length x)) by exact Hc1.
        apply Nat2Z.inj. rewrite Nat2Z.inj_succ. unfold Z.succ. apply (Z.add_cancel_l _ _ x0). rewrite Z.add_assoc. exact Hc1'. }
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x768).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      ws_fin (Nat.succ i).
      -- ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- assert (Hz : skipn (Datatypes.S i) x = []) by (apply skipn_all2; rewrite <- Hend; constructor).
         change (Nat.succ i) with (Datatypes.S i). rewrite (skipn_nth x i 0 Hi), Hz. cbn [PjGrammar.skip]. fold bi. rewrite Hc0.
         reflexivity.
      -- rewrite R10. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- rewrite R12. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- ws_regs_kept.
}
{ (* loop at 0x7d8, exit 0x824 *)
induction k as [|k IH]; intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x i
  Hk Hi HJ Hq1 Hq2 Hq3 Hq4 Hq8 Hx1 Ham Hx2 Hxq H10 H12 H11 H19 H24 H26 H27 H22 Hvq Hgx Hrax Hshq Hwq HMN; [lia|].
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (len := Z.of_nat (length x)) in *.
set (p := x0 + Z.of_nat i) in *.
set (bi := nth i x 0) in *.
destruct (Hgx i Hi) as [Hvb Hbi].
remember (Eimg (Ereg regs [Z_to_bv 64 bi])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 bi]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 EV_WSMASK) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 32) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 bi) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 bi]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (Hsq : SHADOW_OFF <= shadow_addr q < kHighMemBeg)
  by (unfold shadow_addr, SHADOW_OFF, kHighMemBeg; pose proof (Z.div_pos q 8); assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia).
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + (7364 + ?bb))) _ _) _) _ => set (b := bb) end.
assert (HS : st_ok_pi SEGS VAL E (ss_ws b)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (7364 + b))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ws. apply pa_entry_st_ok_full.
  - unfold ws_regs. rewrite HE.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | |] | |] | |];
      try (intros X; discriminate X); cbn [sv_denot]; rewrite <- ?HE.
    + rewrite H10, E12, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + exact H27.
    + exact H22.
  - vm_compute. reflexivity.
  - unfold ws_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 12%nat p E12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) bi); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvb.
    + rewrite (VB 19%nat q E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hwq o Ho)|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 12 0) p); [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvq.
    + assert (Hsq2 : 0 <= shadow_addr q < 2 ^ 47) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
      rewrite (VB 26%nat (shadow_addr q) E26) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (shadow_addr q) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      intros kk0 Hkk0. replace kk0 with 0%nat by lia. rewrite !Z.add_0_r.
      unfold aview in Hshq. destruct (mbyte SEGS (mrestrict (w_H W) mem) (shadow_addr q)) as [bb|] eqn:Hbb;
        [|discriminate Hshq]. cbn [option_map] in Hshq. injection Hshq as Hb0. f_equal. apply bv_eq.
      rewrite Hb0. reflexivity.
  - apply pairwise_disjoint_of_extents. unfold ws_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 12%nat p E12) by lia. rewrite (VB 19%nat q E19) by lia.
    rewrite (VB 26%nat (shadow_addr q) E26) by (unfold SHADOW_OFF, kHighMemBeg in Hsq; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in Ham. unfold kHighMemBeg, SHADOW_OFF in Hsq.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ws_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E11, E19, E26, E24, E32, !unsigned_lit_small
      by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold kHighMemBeg, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS WS_Bx ws_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ws_SH. constructor; [|constructor].
  assert (UBx : U E WS_Bx = SHADOW_OFF) by (unfold WS_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
  assert (Up : U E (SOff 12 0) = p) by (apply (U_atom E 12 p E12); lia).
  unfold shent_ok. cbn [she_m she_lo she_hi]. split.
  - rewrite UBx, Up. intros a Ha. apply (Hrax a). lia.
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. rewrite Up in Ha. rewrite UBx.
    unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof RUN as RUNh. pose proof RUNTO as RUNTOh. pose proof BR as BRh.
pose proof RUNI as RUNIh. pose proof RUNTOI as RUNTOIh.
assert (KM0 : forall y : word, ~ (q <= bv_unsigned y < q + 8) -> mrestrict (w_H W) mem y = mrestrict (w_H W) mem y)
  by (intros; reflexivity).
assert (KG0 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
{ ws_awr. }
clear HF. ws_keep q mem KM0 KG0 KM1 KG1.
psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
- (* 32 < byte: not a blank; the branch goes to the exit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x824).
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  ws_fin i.
  + ws_vq (SOff 12 0). ws_den.
  + rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite (ws_ws_big bi Hc). reflexivity.
  + rewrite R10. ws_den.
  + rewrite R12. ws_den.
  + ws_regs_kept.
- (* byte <= 32: test the mask bit *)
  rewrite branch_ltu_U, U_SLit, (U_atom _ 32 bi) in Hc; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
  change (zcanon 32) with 32 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
  { ws_awr. }
  clear HF. ws_keep q mem KM1 KG1 KM2 KG2.
  psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_true_iff in Hc0.
    paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x824).
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    ws_fin i.
    * ws_vq (SOff 12 0). ws_den.
    * rewrite (skipn_nth x i 0 Hi). cbn [PjGrammar.skip]. fold bi. rewrite Hc0. reflexivity.
    * rewrite R10. ws_den.
    * rewrite R12. ws_den.
    * ws_regs_kept.
  + rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 32 bi) in Hc0; [| cbn [ew ewset Nat.eqb extK]; first [exact E32 | rewrite ?ew_havoc_old by (cbv; lia); exact E32] | lia].
    cbn [zalu_raw] in Hc0. rewrite (ws_mask_bit bi ltac:(lia)) in Hc0. apply negb_false_iff in Hc0.
    paj_run_tok_x_inv RUNIh HS HJ SHOK HMN WS_Bspan.
    { ws_awr. }
    clear HF. ws_keep q mem KM2 KG2 KM3 KG3.
    psrr_branch_tok RUNh BRh HS SHOK WS_Bspan.
    * (* p + 1 <> end: back to the loop's first slot, then the loop's remaining iterations (IH) *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_true_iff, Z.eqb_neq in Hc1.
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x7d8).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      pose proof HS as HSt. unfold st_ok_pi in HSt.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs [Z_to_bv 64 bi] WS_KEPT HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) R10. prreg HS (12%bv : bv 5) R12. prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      assert (Hvq1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) q 8 (x0 + Z.of_nat (Nat.succ i))).
      { ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity. }
      assert (Hw1 : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms)) (q + o)).
      { intros o Ho.
        pose proof (ws_writable_of_st_ok _ _ _ (YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 12 1))]) o
          HSt ltac:(vm_compute; right; left; reflexivity) ltac:(cbn; lia)) as Hw.
        cbn [ms_mem restrict base_val YP09.r_base] in Hw. cbn [ew ewset Nat.eqb extK] in Hw.
        rewrite ?ew_havoc_old in Hw by (cbv; lia). rewrite E19, unsigned_lit_small in Hw by lia. exact Hw. }
      assert (Hsh : forall a, x0 <= a < x0 + len -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF a < kHighMemBeg).
      { intros a Ha. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *. pose proof (Z.div_pos a 8).
        assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
      pmkst HS.
      eapply SRr_mono.
      { eapply (IH W (ms_regs ms) (ms_mem ms) _ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk q x0 x (Nat.succ i));
          try eassumption; try lia.
        all: lazymatch goal with
          | |- getr _ 10 = _ => rewrite R10; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 12 = _ => rewrite R12; ws_den; rewrite unsigned_lit_small by lia; rewrite Hp1; reflexivity
          | |- getr _ 27 = _ => rewrite R27; exact H27
          | |- getr _ 22 = _ => rewrite R22; exact H22
          | |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption
          | |- garr8 _ _ _ _ => apply (ws_garr8_keep _ mem); [|exact Hgx]; intros a Ha; apply (ws_av_raw _ _ _ q KM4); lia
          | |- range_addressable _ _ _ _ =>
              intros a Ha; destruct (Hrax a Ha) as (sv & Hsv & Hok); exists sv; split; [|exact Hok];
              destruct (ws_sh_out _ q (Hsh a Ha) Hq3) as [Hs1 Hs2];
              rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hsv
          | |- aview _ _ _ (shadow_addr _) = _ =>
              destruct (ws_sh_out _ q Hsq Hq3) as [Hs1 Hs2]; rewrite (ws_av_raw _ _ _ q KM4 _ Hs1 Hs2); exact Hshq
          | |- ?g => idtac "WSG_IHleft" g; fail
          end. }
      cbv beta. intros W' c' Hwle (-> & regs2 & mem2 & md2 & i2 & -> & HJ2 & HMN2 & KM5 & KG5 & Hvq2 & Hii & Hsk & H102 & H122 & HK2).
      split; [reflexivity|]. exists regs2, mem2, md2, i2.
      split; [reflexivity|]. split; [exact HJ2|]. split; [exact HMN2|].
      split; [intros y Hn; rewrite (KM5 y Hn); exact (KM4 y Hn)|].
      split; [exact (mem_grows_trans _ _ _ KG4 KG5)|].
      split; [exact Hvq2|]. split; [lia|].
      split; [rewrite Hsk, (skipn_nth x i 0 Hi); cbn [PjGrammar.skip]; fold bi; rewrite Hc0; reflexivity|].
      split; [exact H102|]. split; [exact H122|].
      intros r h1 h2 h3 h4. rewrite (HK2 r h1 h2 h3 h4). revert r h1 h2 h3 h4. ws_regs_kept.
    * (* p + 1 = end: `j exit` *)
      rewrite branch_ne_U, (U_atom_off _ 12 p 1), (U_atom _ 11 (x0 + len)) in Hc1;
        [| cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E11 | lia
         | cbn [ew ewset Nat.eqb extK]; rewrite ?ew_havoc_old by (cbv; lia); exact E12 | lia | lia].
      apply negb_false_iff, Z.eqb_eq in Hc1.
      assert (Hend : Nat.succ i = length x).
      { assert (Hc1' : x0 + Z.of_nat i + 1 = x0 + Z.of_nat (length x)) by exact Hc1.
        apply Nat2Z.inj. rewrite Nat2Z.inj_succ. unfold Z.succ. apply (Z.add_cancel_l _ _ x0). rewrite Z.add_assoc. exact Hc1'. }
      paj_run_to_tok_x_inv RUNTOIh HS HJ SHOK HMN WS_Bspan (7364 + 0x824).
      { ws_awr. }
      clear HF. ws_keep q mem KM3 KG3 KM4 KG4.
      assert (Hp1 : p + 1 = x0 + Z.of_nat (Nat.succ i)) by (rewrite Nat2Z.inj_succ; unfold Z.succ; rewrite Z.add_assoc; reflexivity).
      ws_fin (Nat.succ i).
      -- ws_vq (SOff 12 1). ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- assert (Hz : skipn (Datatypes.S i) x = []) by (apply skipn_all2; rewrite <- Hend; constructor).
         change (Nat.succ i) with (Datatypes.S i). rewrite (skipn_nth x i 0 Hi), Hz. cbn [PjGrammar.skip]. fold bi. rewrite Hc0.
         reflexivity.
      -- rewrite R10. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- rewrite R12. ws_den. rewrite unsigned_lit_small by lia. rewrite Hp1. reflexivity.
      -- ws_regs_kept.
}
Qed.
End d.

(* ======== THE INTERFACE'S TEXT: S8aIface.v ev_ws_loop_spec at image A ========
   From ev_pre / ev_mid / ev_regs at a loop's first slot to ws_loop_raw's premises (the cursor, the text, the struct's
   shadow byte by alx_zshadow_byte, in->p's 8 bytes writable by the journal's present stack window), and back: ev_mid
   at the new cursor by ws_mid_keep, the raw frame as ws_loop_raw gives it. Section hypothesis: LAWS only. *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PI)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
#[local] Notation PRE := (ev_pre (fx := fx) (PI := PI) (L := A_prog_listing) (PA := PA) B ARx).
#[local] Notation MID := (ev_mid (PI := PI) (L := A_prog_listing) (PA := PA) B ARx SK).

(* ---- the frame arithmetic of an activation ---- *)
(* ex_value's stack allowance at image A is at least one ESTACK above its save area *)
Lemma ws_stk : forall n, ESTACK + 288 <= STK_ex_value n.
Proof. intros n. unfold STK_ex_value. vm_compute (zmaxl _). vm_compute (pi_frame _). unfold ESTACK. lia. Qed.

Lemma ws_ev_bounds : forall a ly S Hp W mem md k p dep dl, PRE a -> MID a ly S Hp W mem md k p dep dl ->
  YM05.alloc_ceiling <= ea_sp0 a - ea_STK a /\ ESTACK + 288 <= ea_STK a /\ ea_sp0 a <= ea_q a /\
  ea_q a + 40 <= ea_sp0 a + ea_d a /\ ea_sp0 a + ea_d a <= 2 ^ 47 /\ ea_q a mod 8 = 0 /\ 0 <= ea_d a /\
  ly_stk_lo ly <= ea_sp0 a - ea_STK a /\ ea_sp0 a + ea_d a <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47.
Proof.
intros a ly S Hp W mem md k p dep dl HP HM. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as (((_ & _ & _ & _ & _ & HSTK & _) & _) & _ & _ & _ & _ & _ & HQ8 & _ & HSQ & HQD & HFW & _).
destruct HSTK as (_ & _ & HCEIL & HLO & _ & H47 & _ & HTOP & HTOPHI).
destruct HFW as (HD0 & _ & HDTOP & _).
destruct HM as ((_ & HLY & _) & _).
destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
pose proof (ws_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK.
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
rewrite ESLO, ESHI. repeat split; lia.
Qed.

(* ---- byte transports ---- *)
Lemma ws_vm_keep : forall (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> mbyte SEGS m' z = mbyte SEGS m z) -> val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H kk Hk. rewrite E by lia. exact (H kk Hk). Qed.

(* a shadow byte of an address below 2 ^ 47 lies below the allocator ceiling *)
Lemma ws_sh_lt : forall x, 0 <= x < 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof (asan_consts (rc := rc)) as (C1 & _). unfold SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma ws_ra_keep : forall (rd rd' : reader) a len,
  (forall z, 0 <= z < YM05.alloc_ceiling -> rd' z = rd z) -> 0 <= a -> a + len <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof.
intros rd rd' a len HK H0 H1 H. eapply range_addressable_agree; [|exact H].
intros x Hx. unfold shadow_of_addr. apply HK. apply ws_sh_lt. lia.
Qed.
Lemma ws_hull_keep : forall (rd rd' : reader) a len,
  (forall z, 0 <= z < YM05.alloc_ceiling -> rd' z = rd z) -> 0 <= a -> 0 < len -> a + len <= 2 ^ 47 ->
  shadow_hull_vis rd a len -> shadow_hull_vis rd' a len.
Proof.
intros rd rd' a len HK H0 Hl H1 H s Hs. rewrite HK; [exact (H s Hs)|].
pose proof (asan_consts (rc := rc)) as (C1 & _). unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
assert ((a + len - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos (2147450880 + a / 8) 8 ltac:(lia) ltac:(lia)).
assert ((2147450880 + (a + len - 1) / 8) / 8 < 2 ^ 42) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* the blocks a reader tree owns are lblk blocks (pure; S8aDisp.v's ev_*_blocks over PRH_Reader's predicates) *)
Lemma ws_itemsR_blocks : forall (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  PRH_Reader.pj_itemsR P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros lblk P l. induction l as [|u l IH]; intros a D HP H x k Hin; cbn [PRH_Reader.pj_itemsR] in H.
- subst D. destruct Hin.
- destruct H as (D1 & D2 & -> & HPu & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + exact (HP a u D1 (or_introl eq_refl) HPu x k Hin).
  + apply (IH (a + 56) D2); [|exact Hr|exact Hin]. intros a' u' D1' Hu. apply HP. right. exact Hu.
Qed.
Lemma ws_memsR_blocks : forall segs m (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  PRH_Reader.pj_memsR segs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros segs m lblk P l. induction l as [|[nm u] l IH]; intros a ka D HP H x k Hin; cbn [PRH_Reader.pj_memsR] in H.
- subst D. destruct Hin.
- destruct H as (x0 & k0 & D1 & D2 & -> & _ & (Hl & _) & HPu & Hr).
  destruct Hin as [E|Hin]; [injection E as <- <-; exact Hl|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + exact (HP a nm u D1 (or_introl eq_refl) HPu x k Hin).
  + apply (IH (a + 56) (ka + 8) D2); [|exact Hr|exact Hin]. intros a' nm' u' D1' Hu. apply (HP a' nm' u' D1'). right. exact Hu.
Qed.
Lemma ws_nodeR_blocks : forall segs t m lblk p D, PRH_Reader.pj_nodeR segs m lblk p t D ->
  forall x k, In (x, k) D -> lblk x k.
Proof.
intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H x k Hin;
  cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & H).
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct H as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct H as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct H as (_ & _ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
    destruct Hin as [E|[]]. injection E as <- <-. destruct Hc as [(C1 & _)|(_ & Hl)]; [lia | exact Hl].
  + rewrite Forall_forall in IH.
    apply (ws_itemsR_blocks lblk (PRH_Reader.pj_nodeR segs m lblk) items kids Di); [|exact Hi | exact Hin].
    intros a' u D1 Hu H1. exact (IH u Hu m lblk a' D1 H1).
- destruct H as (_ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
    destruct Hc as [(C1 & _)|(_ & Hl1 & Hl2)]; [lia|].
    destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption.
  + rewrite Forall_forall in IH.
    apply (ws_memsR_blocks segs m lblk (PRH_Reader.pj_nodeR segs m lblk) members kids keys Di); [|exact Hi | exact Hin].
    intros a' nm u D1 Hu H1. exact (IH (nm, u) Hu m lblk a' D1 H1).
Qed.

(* ---- EV_MID across the loop: only in->p's 8 bytes moved (the raw frame), the memory grew ----
   Every byte ev_mid reads outside the caller window lies below q: the statics (prh_img_A's addresses), the ledger's
   heads, the text and the scratch (below alloc_ceiling), the shadow bytes (below alloc_ceiling for an address below
   2 ^ 47), the own frame's flag word (frames_bounds_x), the save area (below sp0). The caller window outside FP misses
   [q, q + 8), which FP holds; the tree's footprint misses [q, q + 40) (ev_pre). *)
Lemma ws_mid_keep : forall a ly S Hp W mem md k p dep dl mem' md' p',
  PRE a -> MID a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall y : word, ~ (ea_q a <= bv_unsigned y < ea_q a + 8) -> mrestrict (w_H W) mem' y = mrestrict (w_H W) mem y) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_q a) 8 p' ->
  YAkMemnorm.memnorm SEGS mem' ->
  MID a ly S Hp W mem' md' k p' dep dl.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' p' HP HM HJ' RAW GROW Vp' HMN'.
pose proof (ws_ev_bounds a ly S Hp W mem md k p dep dl HP HM)
  as (BC & BK & BQ & BQD & B47 & BQ8 & BD0 & BLO & BHI & BH47).
pose proof (asan_consts (rc := rc)) as (C1 & _). unfold ESTACK in BK.
pose proof (@cf_head_nonneg cp) as Hh0.
unfold ev_pre in HP. cbv zeta in HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
destruct HM as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & _).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFR & _).
(* a byte of the word range off [q, q + 8) is kept *)
assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz Hn. unfold mbyte. rewrite (RAW (Z_to_bv 64 z)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (LOW : forall z, 0 <= z < ea_q a ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply KEEP; lia. }
assert (LOWA : forall s, 0 <= s < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. unfold aview. rewrite LOW by lia. reflexivity. }
(* the ledger's blocks lie in [4096, alloc_ceiling) *)
assert (LAMB : forall b mm, In (b, mm) (ea_Lam a) -> 4096 <= b /\ b + mm <= YM05.alloc_ceiling).
{ intros b mm Hin. pose proof HLED as (_ & _ & HF & _).
  destruct (proj1 (Forall_forall _ _) HF (b, mm) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (mm + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
  assert (Hrq : 0 <= mm + cf_head) by lia. apply req_size_pos in Hrq. lia. }
unfold ev_mid.
split; [exact HJ'|].
(* the caller window outside FP: FP holds [q, q + 8) *)
split.
{ intros z Hz Hnf. rewrite <- (HWIN z Hz Hnf). unfold aview. rewrite KEEP; [reflexivity | lia |].
  intros Hq. apply Hnf. exists (ea_q a, ea_q a + 8). split; [unfold ea_FP; right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact HHP|]. split; [exact HABL|].
(* the ledger: the statics at prh_img_A's addresses and the block heads, all below q *)
split.
{ destruct HLED as (HGL & HND & HHB & HPM).
  split; [|split; [exact HND|split; [|exact HPM]]].
  - unfold prh_glob, prh_most, prh_own in HGL |- *.
    cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
      pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_A] in HGL |- *.
    destruct HGL as (V1 & V2 & V3 & V4 & V5 & (V6 & V6r) & (V7 & V7r) & VR).
    split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V1]|].
    split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V2]|].
    split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V3]|].
    split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V4]|].
    split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V5]|].
    (* #102: g_most / g_own_ran_out (PRH_Base.v 3004a98fe2d9 prh_most / prh_own), kept as the five are *)
    split; [split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V6]
      | exact V6r]|].
    split; [split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; cbn in Hz; lia | exact V7]
      | exact V7r]|].
    exact VR.
  - rewrite Forall_forall in HHB |- *. intros [a1 k1] Hin.
    destruct (HHB (a1, k1) Hin) as (Hk0 & Hblk & Hhp & Hal & Hv). cbn [fst snd] in Hk0, Hblk, Hhp, Hal, Hv |- *.
    split; [exact Hk0|]. split; [exact Hblk|]. split; [exact Hhp|]. split; [exact Hal|].
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a1 - cf_head) (k1 + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
    assert (Hrq : 0 <= k1 + cf_head) by lia. apply req_size_pos in Hrq.
    apply (ws_vm_keep (mrestrict (w_H W) mem)); [|exact Hv]. intros z Hz. apply LOW. cbn in Hz. lia. }
(* the cursor: in->p from the loop, the other fields off [q, q + 8) *)
split.
{ destruct HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
  split; [exact Vp'|].
  split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply KEEP; cbn in Hz; lia | exact Q2]|].
  split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply KEEP; cbn in Hz; lia | exact Q3]|].
  split; [apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply KEEP; cbn in Hz; lia | exact Q4]|].
  apply (ws_vm_keep (mrestrict (w_H W) mem)); [intros z Hz; apply KEEP; cbn in Hz; lia | exact Q5]. }
(* the text: below alloc_ceiling *)
split.
{ destruct HSRC as (HBY & H4 & HCE & HAM & HRA & HHU). unfold ea_len in *.
  split; [apply (ws_garr8_keep _ mem); [intros z Hz; apply LOWA; lia | exact HBY]|].
  split; [exact H4|]. split; [exact HCE|]. split; [exact HAM|].
  split; [apply (ws_ra_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | lia | exact HRA]|].
  intros Hl. apply (ws_hull_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | exact Hl | lia | exact (HHU Hl)]. }
(* the scratch: below alloc_ceiling; writability grows *)
split.
{ destruct HWD as (HD0 & HDC & HAM & HWW & HRA & HHU).
  split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM|].
  split; [intros z Hz; destruct (HWW z Hz) as (Hw & Ho & Hs);
    split; [exact (writable_at_grows SEGS _ _ z GROW Hw) | split; [exact Ho | exact Hs]]|].
  split; [apply (ws_ra_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | lia | exact HRA]|].
  intros Hl. apply (ws_hull_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | exact Hl | lia | exact (HHU Hl)]. }
(* the tree: its footprint misses [q, q + 40) (ev_pre) and lies below 2 ^ 47 (its home, the ledger's blocks) *)
split.
{ destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [left; exact Hv0|].
  destruct HTREE as [Hv0|(HN & HH & HRA & HHV)]; [left; exact Hv0|]. right.
  assert (VB : 0 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47).
  { destruct HH as [(bb & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
    - destruct (LAMB bb mm Hin). lia.
    - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (F0 & F1 & _). lia.
    - unfold spZ in H1. pose proof (bv_unsigned_in_range _ (getr (ea_regs a) 2)). lia. }
  split; [|split; [exact HH|split; [apply (ws_ra_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | lia | exact HRA] |
    apply (ws_hull_keep (aview SEGS (w_H W) mem)); [exact LOWA | lia | lia | lia | exact HHV]]]].
  apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
    (prh_lin (ea_Lam a)) (ea_v a) (ea_D a) HN).
  unfold PRH_Reader.pj_agreeR. intros z Hz.
  assert (Hzb : 0 <= z < 2 ^ 47).
  { destruct Hz as [Hz|([xb kb] & Hin & Hhold)]; [lia|].
    pose proof (ws_nodeR_blocks SEGS (ea_t a) _ _ _ _ HN xb kb Hin) as Hl. unfold prh_lin in Hl.
    destruct (LAMB xb kb Hl). unfold PRH_Reader.pj_holdsR in Hhold. cbn [fst snd] in Hhold. lia. }
  assert (Hzq : ~ (ea_q a <= z < ea_q a + 8)).
  { assert (Hf : PjStruct.pj_foot (ea_v a) (ea_D a) z)
      by (destruct Hz as [Hz|(bk & Hin & Hhold)]; [left; exact Hz | right; exists bk; split; [exact Hin | exact Hhold]]).
    destruct (FOOT z Hf) as (_ & Hq & _). lia. }
  split; [apply KEEP; [lia | exact Hzq] | intros Hw; exact (writable_at_grows SEGS _ _ z GROW Hw)]. }
(* the save area [SA + 152, sp0): below q *)
split.
{ unfold ev_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros orr Hin.
  assert (Hb : 152 <= fst orr <= 248).
  { unfold EV_SAVED in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  apply (ws_vm_keep (mrestrict (w_H W) mem)); [|exact (HSAV orr Hin)].
  intros z Hz. apply LOW. unfold ea_SA in Hz. cbn in Hz. lia. }
(* the own frame's flag word: inside a live fake frame, below alloc_ceiling; the room conjunct: S unchanged; memnorm
   at the exit memory (the loop's _inv runners) *)
split; [|split; [exact HROOM | split; [exact HRPOS | exact HMN']]].
{ assert (HIN : In (1, ea_pos a) (frames S)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN) as (F0 & F1 & _).
  assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a).
  { destruct HLY as (_ & _ & _ & _ & _ & ELF & _). unfold ea_fr, frame_addr. rewrite ELF. reflexivity. }
  rewrite EF in F0, F1. assert (FB : fs_frame_bytes 1 = 128) by reflexivity.
  rewrite <- HFLAG. apply rdword_ext. intros kk Hk. apply LOWA. lia. }
Qed.

(* the cut point's configuration in the engine's form *)
Lemma ws_cfg : forall (fxc : YK11.FPState) regs off mem md,
  ev_cfg (L := A_prog_listing) (PA := PA) fxc regs off mem md =
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (7364 + off))) mem (YK11.seg_rom SEGS)) md.
Proof. intros fxc regs off mem md. unfold ev_cfg, ev_pc. rewrite ev_sigma_val, <- Z.add_assoc. reflexivity. Qed.

(* THE SHARED WHITESPACE LOOP, S8aIface.v's text with its raw-frame conjunct *)
Lemma ev_ws_loop : ev_ws_loop_spec (fx := fx) (PI := PI) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros b e Hbe a fxc W regs mem md ly S Hp k i dep dl HP HFX HM HR H10 H12 H11 H27 H22 Hi.
pose proof (ws_ev_bounds a ly S Hp W mem md k _ dep dl HP HM)
  as (BC & BK & BQ & BQD & B47 & BQ8 & BD0 & BLO & BHI & BH47).
pose proof (asan_consts (rc := rc)) as (C1 & _). unfold ESTACK in BK.
pose proof HM as (HJ & _ & _ & _ & _ & (Q1 & _) & (HBY & HX4 & HXC & HAM & HRA & _) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
unfold ea_len in *.
(* struct ex's shadow byte: the real stack's shadow reads 0 *)
assert (HSQ : aview SEGS (w_H W) mem (shadow_addr (ea_q a)) = Some 0).
{ unfold shadow_addr. apply (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md (ea_q a) HAR). lia. }
(* in->p's 8 bytes: inside the journal's present stack window [sp0 - STK, sp0 + d) *)
assert (HWQ : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (ea_q a + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply HPRS. lia. }
eapply SRr_mono.
{ rewrite ws_cfg.
  apply (ws_loop_raw (fx := fxc) (SK := SK) B PST ARx LAWS b e Hbe (length (ea_x a) - i)%nat W regs mem md
    (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp k (ea_q a) (ea_x0 a) (ea_x a) i).
  all: first [reflexivity | eassumption | lia]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & i' & -> & HJ' & HMN' & RAW & GROW & Vq' & Hii & Hsk & R10' & R12' & HK).
split; [reflexivity|]. exists regs', mem', md', i'.
split; [rewrite ws_cfg; reflexivity|].
split; [exact (ws_mid_keep a ly S Hp W mem md k _ dep dl mem' md' _ HP HM HJ' RAW GROW Vq' HMN')|].
split; [exact Hii|]. split; [exact Hsk|]. split; [exact R10'|]. split; [exact R12'|]. split; [exact HK|].
exact RAW.
Qed.
End v.
