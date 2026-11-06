(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 993 of its 1042 lines of code are new or changed and 729 lines of the source are left out. *)
(* fuzz_preset image A, slice S6: the program walk of pj_get (82 instructions) over the ONE image-A program
   listing (lib/A/Listing_prog.v), generic in the image facts (Context PAImg A_prog_listing) and in the allocator
   relation ARx (LAWS : AR_laws_x .. cf_head), concluding the text tpj_get_specX (lib/A/PRH_FnPj.v) from the strcmp
   row at the wrapper's address, in SRr form. The member loop is one lemma at the loop head (pg_loop), by strong
   induction on the members left.
   THE MEMORY INVARIANT (h-hpreset-7's generic-P form, 12:18Z / 12:22Z): Section p walks pj_get_holds_P :
   tpj_get_specXP Pm (BPjGet's generalisation of K0's m-form text, lib/A/Prog/S6PjStrcmp.v section (4),
   origin/cold/h-rw-pre-5-b-pjget b45105596b2 blob c6208f606c8e) for every Pm with srr_inv_laws SEGS Pm and
   srr_inv_call SEGS Pm (the segment crosses the strcmp call; YSRrMemnorm.v, 5ffa8525936b on the kit's cut 7cdbb61b5fa0;
   first from commit 161f89a71b4d). Its runs carry m |-> (Pm mem -> Pm m) (paj_run_x_inv / paj_run_to_x_inv, laws
   YSRrMemnorm.srr_inv_laws_imp); the strcmp call is a Theorem Labs lane's family-1b rule aj_strcmp_at_xrom (YGcallMxmn.v,
   3c08bbab8292 on the cut; first from a working branch 36d44407fa94) over its row astrcmp_realizes_xrom, whose keep is lifted to
   Pm by srr_inv_call. The m-form text (memnorm over YAkMemnorm; on the cut PRH_FnPj.v 5aca5cbe2cfb) is the instance
   pj_get_holds at Pm := YAkMemnorm.memnorm SEGS, by S6PjStrcmp.v's conversion tpj_get_specX_of_P. The old
   statement (the 3f0953cd536 text, not m-form) has no corollary: The TEXT changed (fpostm, and fpre's raZ bound).
   Texts: the kit's cut 7cdbb61b5fa0 (lib/A/PRH_FnPj.v 5aca5cbe2cfb, PRH_Base.v ef7c8ca98529, PRH_Reader.v
   4266e709561a); engine: the cut's set (YCbqG.v 219748197d6b, YGcallMx.v 403da6c072a9, YGcallMxmn.v 3c08bbab8292).
   History: first proved on the kit's preview walkkit-next 04388d628fb with a Theorem Labs lane's set s1b 7792959a2abb. Image-free
   pieces: S6PjCommon.v,
   S6PjStrcmp.v. Section hypotheses (theorem premises): the image facts Hent / Hobj / PAB (discharged at PI_prog_A) and
   the strcmp row ASCR (c-omx-alloc's astrcmp_realizes_xrom, the callee's row).
   RE-FIT 2026-10-29 onto the #102 kit walkkit-next f97c8b2f046b (PRH_FnPj.v 908f34f0beaa, PRH_Base.v fdb45545469b,
   S1Ledger.v 8cf15eeb6311, S6PjStrcmp.v 08bc26a7e4e3): the ledger prh_ledger .. ran most own (g_most, g_own_ran_out)
   is threaded through pg_post / pg_lam_low / pg_ledger_kept / pg_fin / pg_foot / pg_loop, and fpre's last conjunct
   frm_zero (FRM0-ENTRY) is named in the intro pattern.
   Numerals: 80 (LENGTH: pj_get's frame, the pi_frame F_pj_get), 8 .. 72 (LENGTH:
   the nine save slots), 24 / 32 / 40 / 56 (LENGTH: node fields), 6 (WORD: the tag of PjTree.JObj), 8 / 3 / 4
   (LENGTH: word, granule log, stack alignment), the listing offsets of the loop head / branch targets (DERIVED: computed
   from AF_pg); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (DERIVED: shadow and stack bounds); atom indices (DERIVED: the engine's
   numbering). No address literal: addresses are pa_sigma / pa_val of PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnPj CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon S6PjStrcmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* pj_get's offset in the listing (DERIVED: its slot times 4) *)
Definition AF_pg : Z := 4 * Z.of_nat (A_prog_slot AS_pj_get).
Definition PG_Bx : sv := SOff 32 0.
Definition PG_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 80 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition pg_regions : smem := [stack_region 80; got_regionP; bcell_regionP 32].
Definition pg_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pg : sstate := mkSS AF_pg sr_atoms pg_regions None pg_facts.
(* the node's header words the code reads (atom 10 = o): type (atom 33), kids (34), keys (35), n (36) *)
Definition pg_node : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 56 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
(* ---- the member loop's seat, at the loop head (AF_pg + 160): sp (atom 2) is the entry sp - 80, s0 = o (8), s1 = k (9),
   s3 = the shadow base (19, the loop's Bx), s4 = n - i (20), s5 = -56 i (21), s6 = s2 = keys + 8 i (22), s7 = s6's
   shadow address; the frame holds the nine entry registers (atoms 32 .. 40: ra, s0 .. s7); the node's kids word
   (atom 42) and the key pointer keys[i] (atom 41) ---- *)
Definition PL_Bx : sv := SOff 19 0.
Definition pg_saves : list (Z * bv 5) :=
  [(72, 1%bv); (64, 8%bv); (56, 9%bv); (48, 18%bv); (40, 19%bv); (32, 20%bv); (24, 21%bv); (16, 22%bv); (8, 23%bv)].
Definition pg_lframe : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 80 0 0
    (map (fun c => YP09.mkChunk (fst c) (CVal 8 (SOff (snd c) 0)))
      [(8, 40%nat); (16, 39%nat); (24, 38%nat); (32, 37%nat); (40, 36%nat); (48, 35%nat); (56, 34%nat); (64, 33%nat); (72, 32%nat)]).
Definition pg_lnode : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 42 0))].
Definition pg_lkey : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 41 0))].
Definition pg_lfacts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (22%nat, mkAF 4096 (2 ^ 47 - 64) 3)] [] [].
(* the loop head: the frame and the key slot; s7 the shadow address of s6 *)
Definition pg_lsr : list sv := sr_set sr_atoms 23%bv (SAlu ALU_ADD (SOff 19 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3))).
Definition ss_pl : sstate := mkSS (AF_pg + 160) sr_atoms [pg_lframe; pg_lkey] None pg_lfacts.
(* the return point of the strcmp call (AF_pg + 180): the frame and the node's kids word; a0 the result (atom 10) *)
Definition pg_rfacts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (22%nat, mkAF 4096 (2 ^ 47 - 64) 3); (8%nat, mkAF 4096 (2 ^ 47 - 56) 3)] [] [].
Definition ss_pr : sstate := mkSS (AF_pg + 180) sr_atoms [pg_lframe; pg_lnode] None pg_rfacts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).

(* the entry env: the registers, the shadow base (atom 32) and the node header words (atoms 33 .. 36: type, kids, keys,
   n; zero when there is no node) *)
Definition pg_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_A: the entry, the GOT word of the shadow base and the shadow cell in the image,
   the image start *)
Hypothesis Hent : SIGMA AS_pj_get = BASE + AF_pg.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
(* the callee: the strcmp row at the strcmp wrapper, with its memnorm keep (YGcallMxmn.v family 1b) *)
Hypothesis ASCR : astrcmp_realizes_xrom SEGS B ARx (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) (SIGMA AS___wrap_strcmp).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

Lemma pg_frame : STK_pj_get (PI := prh_img_A) = 80 + 2 * ESTACK.
Proof. vm_compute. reflexivity. Qed.

Section p.
(* the memory invariant the walk keeps (the batch instance: YAkMemnorm.memnorm SEGS) *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
(* the segment crosses the strcmp call, whose keep is the memnorm one *)
Hypothesis PCALL : srr_inv_call SEGS Pm.
(* ---- the post: the text's lambda (tpj_get_specXP's, with the keep of Pm from the entry memory mem0), named ---- *)
Definition pg_post (mem0 : word -> option byte) (ly : alayout) (S : astate) (Hp : list Z) (o : Z) (t : jv) (D Lam : list (Z * Z)) (kname : list Z)
  (peak cnt fail ran most own : Z) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' _ =>
  (Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
   prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
   (room_live_cf S -> room_live_cf S') /\
   (o = 0 /\ getr regs' 10 = w64 0 \/
    o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) o t D /\
    exists z, getr regs' 10 = w64 z /\ prhPj_get_res (PA := PA) (mrestrict (w_H W') mem') (prh_lin Lam) o t D kname z)) /\
  (Pm mem0 -> Pm mem').
(* the callee-saved registers (YG0d.v acallee_saved), as register names *)
Definition pg_all : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma pg_aregs : forall (regs regsF : bvmap 5 word),
  (forall r : bv 5, In r pg_all -> getr regsF r = getr regs r) -> aregs_preserved regs regsF.
Proof.
intros regs regsF H r Hr. apply H. unfold pg_all. apply in_map. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto .. |].
assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H0 as [-> | H0]; [cbn; tauto|]). subst r. cbn; tauto.
Qed.
(* alloc.c's statics (prh_img_A's generated addresses) are below alloc_ceiling *)
Lemma pg_pst_low : forall a, Exists (in_zr a) PST -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* a harness block of the ledger lies below alloc_ceiling, its head too *)
Lemma pg_lam_low : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 4096 <= a - 16 /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
    In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & Hhp & _).
change (@cf_head CP) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
rewrite gs_req in Hc by lia. repeat split; try lia; assumption.
Qed.
(* the ledger at a memory that agrees below alloc_ceiling *)
Lemma pg_ledger_kept : forall ly S Hp W mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HL KL.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HL).
- intros a Ha. apply KL. exact (pg_pst_low a Ha).
- intros a k0 i Hin Hi. change (@cf_head CP) with 16.
  destruct (pg_lam_low ly S Hp W mem md Lam peak cnt fail ran most own a k0 HAR HL Hin) as (H4 & Hk0 & Hc & _).
  pose proof asan_consts as (C1 & _). apply KL. lia.
- intros a k0 _ H. exact H.
- apply Permutation_refl.
Qed.
(* every exit: the registers back, the journal from the entry, the memory below alloc_ceiling as at entry *)
Lemma pg_fin : forall ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ (STK_pj_get (PI := prh_img_A)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memF mdF k0 ->
  (Pm mem -> Pm memF) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall r : bv 5, In r pg_all -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  getr regsF 10%bv = w64 res ->
  (o = 0 /\ res = 0 \/ o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o t D /\
     prhPj_get_res (PA := PA) (mrestrict (w_H W) memF) (prh_lin Lam) o t D kname res) ->
  fpost (PI := prh_img_A) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_A)) [] regs ly S Hp W mem md
    (pg_post mem ly S Hp o t D Lam kname peak cnt fail ran most own) W
    (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res
  HAR HLED HJ HPMF KL Hra Hkept G1 G10 HR.
unfold fpost, apost_base_x.
exists ly, S, Hp, regsF, memF, (with_vm_backing (m_vm_lazy mdF) mat mdF), k0.
split; [rewrite G1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact (pg_aregs regs regsF Hkept)|].
unfold pg_post. split; [|exact HPMF]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (pg_ledger_kept ly S Hp W mem md memF Lam peak cnt fail ran most own HAR HLED KL)|].
split; [intros H; exact H|].
destruct HR as [(Ho0 & ->) | (Hon & Hnd & Hres)]; [left; split; [exact Ho0 | exact G10]|].
right. split; [exact Hon|]. split; [exact Hnd|]. exists res. split; [exact G10 | exact Hres].
Qed.

Lemma pg_entry : forall ly S Hp W (regs : bvmap 5 word) mem md ch xs,
  afn_pre_x SEGS B ARx (STK_pj_get (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (pg_E regs xs) ss_pg (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pg)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PG_Bx [] (pg_E regs xs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch xs HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (Hobj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
pose proof pg_frame as FS.
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := pg_E regs xs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold pg_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold pg_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold pg_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_pg. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pg_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PG_Bx SHADOW_OFF);
    [cbn [sv_denot PG_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold pg_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pg_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the tree's footprint (header and blocks) is off the image and outside pj_get's stack window *)
Lemma pg_foot : forall ly S Hp W mem md regs o t D Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_A) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) o t D ->
  prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_A)) ly S W regs mem o ->
  forall x, pj_footR o D x ->
  0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= x < spZ regs).
Proof.
intros ly S Hp W mem md regs o t D Lam peak cnt fail ran most own HAR HL Hlo Hn Hrs x Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hrs as (H4096 & Hplace & Hamr & Hwin & _).
assert (Hamr' : o + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
destruct Hx as [Hx | (b & Hb & Hx)].
- split; [lia|]. split; [|exact (Hwin x Hx)].
  destruct Hplace as [(p & n & Hin & Hp1 & Hp2) | [(cid & pos & Hin & Hp1 & Hp2) | (Hsp1 & Hsp2)]].
  + refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_introl _))).
    exists p, n. split; [exact Hin | lia].
  + refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_intror (or_introl _)))).
    exists cid, pos. split; [exact Hin | lia].
  + intros Himg. pose proof (@pa_segs_low _ _ PA x Himg). pose proof pg_frame.
    assert (ESTACK = 4096) by reflexivity. unfold kLowMemEnd in *. lia.
- pose proof (pj_nodeR_lblk t _ _ _ _ Hn b Hb) as Hl. unfold prh_lin in Hl. destruct b as [a0 k0].
  destruct (pg_lam_low ly S Hp W mem md Lam peak cnt fail ran most own a0 k0 HAR HL Hl) as (H4 & Hk0 & Hc & Hab & _).
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  split; [lia|]. split; [|lia].
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_introl _))).
  exists (a0 - 16), (k0 + 16). split; [exact Hab|]. rewrite gs_req by lia. lia.
Qed.

(* the loop seat's env: the loop-head registers, then the nine entry registers (32 .. 40), keys[i] (41), kids (42) *)
Definition pl_E (regsL : bvmap 5 word) (xs : list Z) : env := @Eimg _ A_prog_listing PA (Ereg regsL (map (Z_to_bv 64) xs)).

(* the registers at an exit of the loop: the epilogue restores ra, s0 .. s7 from the frame (atoms 32 .. 40), sp is the
   loop head's + 80, and gp, tp, s8 .. s11 are the loop head's *)
Definition pl_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 1 => SOff 32 0 | 2 => SOff 2 80 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0 | 19 => SOff 36 0
  | 20 => SOff 37 0 | 21 => SOff 38 0 | 22 => SOff 39 0 | 23 => SOff 40 0 | z => SOff (Z.to_nat z) 0 end.
Lemma pl_fin_regs : forall (H : word -> bool) E' ss msF (regs regs2 : bvmap 5 word) x kids,
  st_ok_pi SEGS VAL E' ss (restrict H msF) ->
  (forall n, (n < 512)%nat -> ew E' n = ew (pl_E regs2 (map (fun r : bv 5 => bv_unsigned (getr regs r))
     [1%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv] ++ [x; kids])) n) ->
  (forall r, In r (1%bv :: pg_all) -> sr_get (ss_regs ss) r = pl_expect r) ->
  getr regs2 2%bv = Z_to_bv 64 (spZ regs - 80) -> 80 <= spZ regs ->
  (forall r : bv 5, In r (map (Z_to_bv 5) [3; 4; 24; 25; 26; 27]) -> getr regs2 r = getr regs r) ->
  forall r, In r (1%bv :: pg_all) -> getr (ms_regs msF) r = getr regs r.
Proof.
intros H E' ss msF regs regs2 x kids HS HE HX R2 Hsp RK r Hr.
rewrite (st_ok_pi_restrict_reg H E' ss msF r HS), (HX r Hr).
assert (Hr' := Hr). unfold pg_all in Hr'. cbn [map In] in Hr'.
repeat (destruct Hr' as [<- | Hr'];
  [ lazymatch goal with |- sv_denot _ (pl_expect ?rr) = _ =>
      let e := eval vm_compute in (pl_expect rr) in change (pl_expect rr) with e end;
    cbn [sv_denot]; rewrite HE by lia; unfold pl_E; rewrite Eimg_low by (unfold A_TEXT; lia);
    lazymatch goal with |- context [ew (Ereg ?R ?l) ?n] =>
      let kk := eval vm_compute in (Nat.leb 32 n) in
      lazymatch kk with
      | true => let j := eval vm_compute in (n - 32)%nat in
                replace n with (32 + j)%nat by reflexivity; rewrite ew_Ereg_extra; cbn [nth map app];
                rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; f_equal; apply bv_eq; vm_compute; reflexivity
      | false => let z := eval vm_compute in (Z.of_nat n) in
                 rewrite (ew_Ereg_nat R l n (Z_to_bv 5 z) ltac:(vm_compute; reflexivity));
                 first
                   [ (* sp *) replace (Z_to_bv 5 z) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
                     rewrite R2, unsigned_lit_small by (pose proof (bv_unsigned_in_range 64 (getr regs 2%bv)) as Hb;
                       unfold bv_modulus in Hb; change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb; unfold spZ in *; lia);
                     replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ;
                     rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; vm_compute; reflexivity
                   | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite RK; [f_equal; apply bv_eq; vm_compute; reflexivity|];
                     cbn [map In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]
      end end |]).
destruct Hr'.
Qed.

(* a register of a state, rewritten to its expression, computed *)
Ltac gr GR := rewrite GR; lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
(* a register of a st_ok state over a restricted machine, its expression computed *)
Ltac creg SG H HS r C := pose proof (st_ok_restrict_reg SG H _ _ _ r HS) as C;
  lazymatch type of C with _ = sv_denot ?E' ?e => let e' := eval vm_compute in e in change e with e' in C end.

(* ---- the member loop, from the loop head with i members done ---- *)
Lemma pg_loop : forall ly S Hp W regs mem md o k kname members D Lam peak cnt fail ran most own kids keys cap0 Di,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  YK0s.ret_ok (getr regs 1) -> 2 ^ 46 + 80 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_A) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  o <> 0 -> pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) o (JObj members) D ->
  prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_A)) ly S W regs mem o ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (o + 24) kids -> rd_u64 SEGS (mrestrict (w_H W) mem) (o + 32) keys ->
  Z.of_nat (length members) <= cap0 -> In (kids, 56 * cap0) Lam -> In (keys, 8 * cap0) Lam -> incl Di D ->
  pj_memsR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) (pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam)) kids keys members Di ->
  cstr_ok (PA := PA) W mem k kname ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  forall j i regsL memL mdL k0,
  (length members - i = j)%nat -> (i < length members)%nat ->
  AJ (STK_pj_get (PI := prh_img_A)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memL mdL k0 ->
  (Pm mem -> Pm memL) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a) ->
  (forall off r, In (off, r) pg_saves -> val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 80 + off) 8 (bv_unsigned (getr regs r))) ->
  getr regsL 2%bv = Z_to_bv 64 (spZ regs - 80) -> getr regsL 8%bv = w64 o -> getr regsL 9%bv = w64 k ->
  getr regsL 19%bv = Z_to_bv 64 SHADOW_OFF ->
  getr regsL 20%bv = Z_to_bv 64 (Z.of_nat (length members) - Z.of_nat i) ->
  getr regsL 21%bv = Z_to_bv 64 (-56 * Z.of_nat i) ->
  getr regsL 22%bv = Z_to_bv 64 (keys + 8 * Z.of_nat i) -> getr regsL 18%bv = Z_to_bv 64 (keys + 8 * Z.of_nat i) ->
  getr regsL 23%bv = Z_to_bv 64 (SHADOW_OFF + (keys + 8 * Z.of_nat i) / 8) ->
  (forall r : bv 5, In r (map (Z_to_bv 5) [3; 4; 24; 25; 26; 27]) -> getr regsL r = getr regs r) ->
  (forall j' nm u, (j' < i)%nat -> nth_error members j' = Some (nm, u) -> nm <> kname) ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_pg + 160))) memL (seg_rom SEGS)) mdL)
    (fpost (PI := prh_img_A) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_A)) [] regs ly S Hp W mem md
      (pg_post mem ly S Hp o (JObj members) D Lam kname peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md o k kname members D Lam peak cnt fail ran most own kids keys cap0 Di
  HAR HLED Hra Hsp Hal16 Hlo Hgp Htp Hon Hnode Hrs Hkids Hkeys Hcap HKD HKY HDi Hmems HK HROD.
intros j. induction j as [j IH] using lt_wf_ind.
intros i regsL memL mdL k0 Hj Hi HJ HPM KC HFW R2 R8 R9 R19 R20 R21 R22 R18 R23 RK Hpre.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pg_frame as FS. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
(* the i-th member: its key pointer x in keys, its key string, its node *)
destruct (nth_error members i) as [[nm u]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
destruct (pjs_mems_nth _ _ _ _ _ _ _ _ _ _ Hmems Ei) as (x & kx & D1 & (Hx0 & Hxw) & Hxs & Hxu & HD1 & HxD).
(* the keys block: a live harness block below alloc_ceiling, off the image *)
destruct (pjs_lam_blk (PI := prh_img_A) B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own keys (8 * cap0) HAR HLED HKY)
  as (Hk16 & Hk4 & _ & Hkc & Happk & Habk & Hhpk & Hbsk & Hhuk & Hprk & Htlk).
assert (Hkimg : forall a, keys <= a < keys + 8 * cap0 -> ~ in_img SEGS a).
{ intros a Ha. refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR (or_introl _))).
  exists (keys - 16), (8 * cap0 + 16). split; [exact Habk|]. rewrite gs_req by lia. lia. }
set (sl := keys + 8 * Z.of_nat i).
assert (Hsl : keys <= sl /\ sl + 8 <= keys + 8 * cap0) by (subst sl; lia).
assert (Hxw1 : val_mem SEGS (mrestrict (w_H W) memL) sl 8 x).
{ intros t Ht. rewrite <- (Hxw t Ht). fold sl.
  unfold mbyte. rewrite (gs_raw_of_aview (w_H W) (w_H W) mem memL (sl + Z.of_nat t)); [reflexivity | lia | apply Hkimg; lia |].
  apply KC; lia. }
(* ---- the loop-head seat ---- *)
set (xs := map (fun r : bv 5 => bv_unsigned (getr regs r)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv]
  ++ [x; kids]).
set (E := pl_E regsL xs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold pl_E; apply Eimg_low; exact Hn).
assert (F2 : ew E 2 = getr regsL 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (F19 : ew E 19 = getr regsL 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 19 19%bv eq_refl)).
assert (F22 : ew E 22 = getr regsL 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 22 22%bv eq_refl)).
assert (FX : forall j0, (j0 < 11)%nat -> ew E (32 + j0) = Z_to_bv 64 (nth j0 xs 0)).
{ intros j0 Hj0. rewrite EL by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  rewrite <- (map_nth (Z_to_bv 64) xs 0 j0).
  first [reflexivity | apply nth_indep; rewrite length_map; unfold xs; rewrite length_app, length_map; cbn; lia]. }
assert (FXa : forall n0, (32 <= n0 < 43)%nat -> ew E n0 = Z_to_bv 64 (nth (n0 - 32) xs 0)).
{ intros n0 Hn0. replace n0 with (32 + (n0 - 32))%nat at 1 by lia. apply FX. lia. }
assert (USL : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite F2, R2; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = sl) by (rewrite F22, R22; apply unsigned_lit_small; subst sl; lia).
assert (HS0 : st_ok_pi SEGS VAL E ss_pl
  (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + (AF_pg + 160))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pl. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, pg_lframe, pg_lkey;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val map fst snd].
    + rewrite USL. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      repeat (apply Forall_cons;
        [ eapply chunk_ok_val;
          [ cbn [sv_denot]; rewrite FXa by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | unfold xs; cbn [nth app map Nat.sub];
            lazymatch goal with |- 0 <= bv_unsigned ?w < _ =>
              pose proof (bv_unsigned_in_range 64 w) as Hw; unfold bv_modulus in Hw;
              change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia end
          | cbn; lia
          | unfold xs; cbn [nth app map Nat.sub]; change (N.to_nat 8) with 8%nat; apply HFW;
            unfold pg_saves; cbn [In]; repeat (first [left; reflexivity | right]) ] |]).
      apply Forall_nil.
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sl 0 8 (SOff 41 0) x);
        [cbn [sv_denot]; rewrite (FXa 41%nat) by lia; unfold xs; cbn [nth app map Nat.sub];
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact Hxw1.
  - apply pairwise_disjoint_of_extents. unfold pg_lframe, pg_lkey, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite USL, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [pg_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite USL, U22, F19, R19, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; subst sl; lia. }
(* s7 as the shadow address of s6, the shape the token engine matches *)
assert (G23e : getr regsL 23%bv = sv_denot E (SAlu ALU_ADD (SOff 19 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))).
{ apply (gs_reg_shadow_of E 19 22 SHADOW_OFF sl);
    [rewrite F19; exact R19 | rewrite F22; exact R22 | unfold SHADOW_OFF; lia | subst sl; lia | unfold SHADOW_OFF; subst sl; lia | exact R23]. }
pose proof (gs_set_reg (PA := PA) E ss_pl _ 23%bv _ HS0 ltac:(cbn [ms_regs restrict mkst]; exact G23e) eq_refl) as HS.
clear HS0.
assert (SHOK : sh_ok SEGS PL_Bx [] E (mrestrict (w_H W) memL)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pl_E; apply Eimg_env).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
(* ---- slots 40-44: the shadow byte of keys[i], keys[i], a1 = k, jal strcmp ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan.
all: try gs_awr0.
all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
  cbn [ms_mem]; unfold PL_Bx;
  rewrite (U_atom E 19 SHADOW_OFF (eq_trans F19 R19) ltac:(unfold SHADOW_OFF; lia));
  rewrite (U_atom E 22 sl (eq_trans F22 R22) ltac:(subst sl; lia));
  change (rd_of SEGS (mrestrict (w_H W) memL)) with (aview SEGS (w_H W) memL);
  eapply range_addressable_agree; [| exact (block_shadow_range _ _ keys (8 * cap0) sl 8 Hbsk ltac:(lia) ltac:(lia))];
  intros y Hy; pose proof (gs_shadow_low y ltac:(subst sl; lia)); apply KC; lia).
(* ---- the strcmp call ---- *)
gs_memeq HF EMc. clear HF HG HFr.
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hmk.
assert (EN : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (ewset E 512 w) (SOff n 0) = getr regsL r).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite ew_ewset_other by lia. rewrite EL by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regsL _ n r Hr). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (1%bv : bv 5) K1. creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (2%bv : bv 5) K2.
creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (3%bv : bv 5) K3. creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (4%bv : bv 5) K4.
creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (10%bv : bv 5) K10. creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (11%bv : bv 5) K11.
rewrite (EN 2%nat 2%bv) in K2 by (lia || reflexivity). rewrite (EN 3%nat 3%bv) in K3 by (lia || reflexivity).
rewrite (EN 4%nat 4%bv) in K4 by (lia || reflexivity). rewrite (EN 9%nat 9%bv) in K11 by (lia || reflexivity).
assert (K10x : getr (ms_regs ms) 10 = w64 x).
{ rewrite K10. cbn [sv_denot]. rewrite ew_ewset_other by lia. rewrite (FXa 41%nat) by lia. unfold xs; cbn [nth app map Nat.sub].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (K1r : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_pg + 180))).
{ rewrite K1. cbn [sv_denot]. rewrite ew_ewset_other by lia.
  rewrite (img_env_codeptr (PI := PA) E HEI). f_equal; f_equal; vm_compute; reflexivity. }
assert (Csp : spZ (ms_regs ms) = spZ regs + -80).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2%bv)). rewrite K2, R2. rewrite unsigned_lit_small by lia. lia. }
assert (K11k : getr (ms_regs ms) 11 = w64 k) by (rewrite K11; exact R9).
assert (K3g : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite K3, (RK 3%bv); [exact Hgp|]. cbn [map In]. left. apply bv_eq. vm_compute. reflexivity. }
assert (K4t : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite K4, (RK 4%bv); [exact Htp|]. cbn [map In]. right. left. apply bv_eq. vm_compute. reflexivity. }
lazymatch eval vm_compute in (AF_pg + 180) with ?nr => assert (EAF : AF_pg + 180 = nr) by (vm_compute; reflexivity) end.
(* the memory at the call: as at entry outside the window *)
pose proof HJ as (HART & _).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) by (rewrite EMc; exact KC).
assert (KTL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KT; lia).
assert (HLEDT := pg_ledger_kept ly S Hp W mem md (ms_mem ms) Lam peak cnt fail ran most own HAR HLED KTL).
assert (HKT := gs_cstr_kept W W mem (ms_mem ms) k kname HK KTL).
assert (HRODT := gs_rod_kept B W W mem (ms_mem ms) HROD KTL).
(* the key string at the call's memory *)
pose proof Hxs as (Hxl & _).
pose proof Hxl as Hxl'. unfold prh_lin in Hxl'.
destruct (pjs_lam_blk (PI := prh_img_A) B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own x kx HAR HLED Hxl')
  as (Hx16 & Hx4 & _ & Hxc & _ & Habx & _).
assert (Hxs' : pj_cstrR SEGS (mrestrict (w_H W) (ms_mem ms)) (prh_lin Lam) x kx nm).
{ apply (pj_cstrR_frame SEGS (mrestrict (w_H W) mem)); [exact Hxs|].
  intros y Hy. unfold mbyte. rewrite (gs_raw_of_aview (w_H W) (w_H W) mem (ms_mem ms) y); [reflexivity | lia | | apply KTL; lia].
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md y HAR (or_introl _))).
  exists (x - 16), (kx + 16). split; [exact Habx|]. rewrite gs_req by lia. lia. }
assert (HspT : YM05.alloc_ceiling + 2 * ESTACK <= spZ (ms_regs ms)) by (rewrite Csp; lia).
destruct (pjs_key_strcmp_pre (PI := prh_img_A) B ARx LAWS ly S Hp W (ms_mem ms) _ (ms_regs ms) Lam peak cnt fail ran most own x kx nm
  HART HLEDT Hxs' HspT)
  as (Px0 & Pkx0 & Pkx32 & Pxk & Pfx & Psx & Pbx & Pmx & Prx & Phx & Ptx).
destruct (pjs_k_strcmp_pre W (ms_regs ms) (ms_mem ms) k kname HKT HspT)
  as (Py0 & Pky0 & Pky32 & Pyk & Pfy & Psy & Pby & Pmy & Pry & Phy & Pty).
rewrite Hmk. cbn [ss_pc setpc].
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) SEGS B PST ARx (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) LAWS Hsegs
    (SIGMA AS___wrap_strcmp) ASCR W (ms_regs ms) (ms_mem ms)
    (STK_pj_get (PI := prh_img_A)) (spZ regs) [] ly S Hp W mem md [] ly S Hp _ k0 x k
    (Z.of_nat (length nm)) (Z.of_nat (length kname)) (-80) _ HJ K10x K11k Px0 Py0 Pkx0 Pkx32 Pxk Pky0 Pky32 Pyk Csp
    ltac:(reflexivity) ltac:(lia) ltac:(rewrite FS; lia) K3g K4t K1r
    ltac:(apply (ret_ok_codeptr_v (PI := PA)); rewrite EAF; [lia | reflexivity])
    Pfx Pfy Psx Psy ltac:(intros a Ha; rewrite <- Csp; exact (Pbx a Ha)) ltac:(intros a Ha; rewrite <- Csp; exact (Pby a Ha))
    Pmx Pmy Prx Phx Pry Phy Ptx Pty HRODT). }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hiff & Hfr2 & Hpres2 & HK2).
(* the invariant across the call: the run's, then the row's keep *)
assert (HPM2 : Pm mem -> Pm mem2) by (intros h; exact (PCALL _ _ HK2 (HPM h))). clear HPM HK2. rename HPM2 into HPM.
(* ---- the return point (AF_pg + 180) ---- *)
(* the registers the call keeps: the loop head's *)
assert (HAEc : env_agree 32 (Ereg regsL (map (Z_to_bv 64) xs)) (ewset E 512 w)).
{ split; [intros n Hn; rewrite ew_ewset_other by lia; subst E; unfold pl_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
pose proof (regs_kept_of_st_ok SEGS (ewset E 512 w) _ _ regsL (map (Z_to_bv 64) xs)
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAEc
  ltac:(vm_compute; reflexivity)) as KKc.
cbn [ms_regs restrict] in KKc.
assert (QS : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ =>
       let z := eval vm_compute in (bv_unsigned rr) in
       pose proof (HP2 z ltac:(unfold acallee_saved; lia)) as H;
       replace (Z_to_bv 5 z) with rr in H by (apply bv_eq; reflexivity); exact H end |]). destruct Hr. }
assert (QL : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs2 r = getr regsL r).
{ intros r Hr. rewrite QS by (repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr). apply KKc. exact Hr. }
creg (@pa_segs _ A_prog_listing PA) (w_H W) HS (23%bv : bv 5) K23.
assert (Q23 : getr regs2 23%bv = Z_to_bv 64 (SHADOW_OFF + sl / 8)).
{ rewrite QS by (cbn; tauto). rewrite K23, (denot_lit_U (ewset E 512 w)).
  rewrite (gs_U_shadow_of (ewset E 512 w) 19 22 SHADOW_OFF sl); [reflexivity | | | unfold SHADOW_OFF; lia | subst sl; lia | unfold SHADOW_OFF; subst sl; lia].
  - rewrite ew_ewset_other by lia. rewrite F19. exact R19.
  - rewrite ew_ewset_other by lia. rewrite F22. exact R22. }
(* the memory at the return: as at entry outside the window *)
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hw. rewrite (Hfr2 a Ha) by (intros Hc; apply Hw; rewrite FS; lia). exact (KT a Ha Hw). }
assert (HFW2 : forall off r, In (off, r) pg_saves ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 80 + off) 8 (bv_unsigned (getr regs r))).
{ intros off r Hin t Ht. rewrite <- (HFW off r Hin t Ht).
  assert (Hoff : 8 <= off <= 72).
  { unfold pg_saves in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
  unfold mbyte. rewrite (gs_raw_of_aview (w_H W) (w_H W) memL mem2 (spZ regs - 80 + off + Z.of_nat t)); [reflexivity | lia | |].
  - intros Himg. pose proof (Hsegs _ Himg). unfold kLowMemEnd in *. lia.
  - rewrite (Hfr2 (spZ regs - 80 + off + Z.of_nat t)) by lia. rewrite EMc. reflexivity. }
destruct Hrs as (Ho4096 & Hplace & Hamr & Hwin & HRA & HHU).
assert (Ho47 : o + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hk2 : val_mem SEGS (mrestrict (w_H W) mem2) (o + 24) 8 kids).
{ intros t Ht. rewrite <- (proj2 Hkids t Ht). unfold mbyte.
  assert (Hft : pj_footR o D (o + 24 + Z.of_nat t)) by (left; lia).
  destruct (pg_foot ly S Hp W mem md regs o (JObj members) D Lam peak cnt fail ran most own HAR HLED Hlo Hnode
    (conj Ho4096 (conj Hplace (conj Hamr (conj Hwin (conj HRA HHU))))) _ Hft) as (Hr & Hni & Hw).
  rewrite (gs_raw_of_aview (w_H W) (w_H W) mem mem2); [reflexivity | exact Hr | exact Hni | exact (KM2 _ Hr Hw)]. }
destruct (gs_node_hdr _ _ _ _ _ Hnode) as (num0 & str0 & kd0 & ky0 & nn0 & cp0 & ((Hal8 & _) & _)).
assert (Dfr : o + 56 <= spZ regs - 80 \/ spZ regs <= o).
{ destruct (Z_le_gt_dec (o + 56) (spZ regs - 80)); [left; lia|]. destruct (Z_le_gt_dec (spZ regs) o); [right; lia|].
  exfalso. destruct (Z_le_gt_dec o (spZ regs - 80)); [apply (Hwin (spZ regs - 80)) | apply (Hwin o)]; rewrite ?FS; lia. }
set (E2 := pl_E regs2 xs).
assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2 n = ew (Ereg regs2 (map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E2; unfold pl_E; apply Eimg_low; exact Hn).
assert (FR : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r).
{ intros n r Hn Hr. rewrite EL2 by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n r Hr). }
assert (FXa2 : forall n0, (32 <= n0 < 43)%nat -> ew E2 n0 = Z_to_bv 64 (nth (n0 - 32) xs 0)).
{ intros n0 Hn0. rewrite EL2 by (unfold A_TEXT; lia). replace n0 with (32 + (n0 - 32))%nat at 1 by lia. rewrite ew_Ereg_extra.
  rewrite <- (map_nth (Z_to_bv 64) xs 0 (n0 - 32)).
  first [reflexivity | apply nth_indep; rewrite length_map; unfold xs; rewrite length_app, length_map; cbn; lia]. }
assert (USL2 : bv_unsigned (ew E2 2) = spZ regs - 80).
{ rewrite (FR 2%nat 2%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R2. apply unsigned_lit_small. lia. }
assert (U8 : bv_unsigned (ew E2 8) = o).
{ rewrite (FR 8%nat 8%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R8. apply unsigned_lit_small. lia. }
assert (HS2 : st_ok_pi SEGS VAL E2 ss_pr
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (AF_pg + 180))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pr. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, pg_lframe, pg_lnode;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val map fst snd].
    + rewrite USL2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      repeat (apply Forall_cons;
        [ eapply chunk_ok_val;
          [ cbn [sv_denot]; rewrite FXa2 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | unfold xs; cbn [nth app map Nat.sub];
            lazymatch goal with |- 0 <= bv_unsigned ?w < _ =>
              pose proof (bv_unsigned_in_range 64 w) as Hw; unfold bv_modulus in Hw;
              change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia end
          | cbn; lia
          | unfold xs; cbn [nth app map Nat.sub]; change (N.to_nat 8) with 8%nat; apply HFW2;
            unfold pg_saves; cbn [In]; repeat (first [left; reflexivity | right]) ] |]).
      apply Forall_nil.
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E2 _ o 24 8 (SOff 42 0) kids);
        [cbn [sv_denot]; rewrite (FXa2 42%nat) by lia; unfold xs; cbn [nth app map Nat.sub];
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (proj1 Hkids) | lia | exact Hk2].
  - apply pairwise_disjoint_of_extents. unfold pg_lframe, pg_lnode, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite USL2, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [pg_rfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite USL2, U8.
    rewrite (FR 19%nat 19%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R19.
    rewrite (FR 22%nat 22%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R22.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; subst sl; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; subst sl; lia. }
assert (SHOK2 : sh_ok SEGS PL_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; unfold pl_E; apply Eimg_env).
assert (U10 : U E2 (SOff 10 0) = bv_unsigned v).
{ rewrite U_SOff, (FR 10%nat 10%bv) by (lia || reflexivity). rewrite Hv, Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 v) as Hw. unfold bv_modulus in Hw. unfold M64. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw. lia. }
(* the registers the exits restore through pl_fin_regs: gp, tp, s8 .. s11 as at entry *)
assert (RK2 : forall r : bv 5, In r (map (Z_to_bv 5) [3; 4; 24; 25; 26; 27]) -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (RK r Hr). pose proof Hr as Hr0. cbn [map In] in Hr0.
  repeat (destruct Hr0 as [<- | Hr0];
    [ lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        rewrite (HP2 z ltac:(unfold acallee_saved; lia)); apply KKc; cbn [In];
        repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) end |]). destruct Hr0. }
assert (R2' : getr regs2 2%bv = Z_to_bv 64 (spZ regs - 80)) by (rewrite QL by (cbn; tauto); exact R2).
(* the tree at a memory read the same as mem2 outside the window *)
assert (NODEK : forall memF, (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
    aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
  pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o (JObj members) D).
{ intros memF KF. apply (gs_node_kept W mem memF _ o (JObj members) D Hnode). intros y Hy.
  destruct (pg_foot ly S Hp W mem md regs o (JObj members) D Lam peak cnt fail ran most own HAR HLED Hlo Hnode
    (conj Ho4096 (conj Hplace (conj Hamr (conj Hwin (conj HRA HHU))))) y Hy) as (Hr & Hni & Hw).
  split; [exact Hr|]. split; [exact Hni|]. exact (KF y Hr Hw). }
(* slot 45: beqz a0 on the strcmp result *)
psrr_branch_tok RUN BR HS2 SHOK2 PG_Bspan.
- (* found: the member's name is kname; a0 = kids + 56 i *)
  rewrite branch_eq_U, U_SLit, U10 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc.
  assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  pose proof Hxs' as (_ & _ & _ & _ & Hxg').
  pose proof HKT as ((Hkg' & _) & _).
  assert (Enm : nm = kname) by (apply (proj1 (pjs_strcmp_iff W (ms_mem ms) x nm k kname Hxg' Hkg')); exact (proj1 Hiff Hv0)).
  subst nm.
  paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM PG_Bspan.
  all: try gs_awr0.
  { cbn [ms_mem]. unfold PL_Bx. rewrite !U_SOff. rewrite ?ew_ewset_other by lia.
    rewrite (FR 19%nat 19%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R19.
    rewrite (FR 8%nat 8%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R8. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
    change (rd_of SEGS (mrestrict (w_H W) mem2)) with (aview SEGS (w_H W) mem2).
    eapply range_addressable_sub; [eapply range_addressable_agree; [| exact HRA] | lia | lia].
    intros y Hy. apply KM2; cbv [shadow_of_addr SHADOW_OFF]; rewrite ?FS; lia. }
  (* slots 64 .. 74: a0 = kids - s5, the nine registers back, ret *)
  gs_memeq HF EMf. clear HF HG HFr.
  eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  destruct (pg_lam_low ly S Hp W mem md Lam peak cnt fail ran most own kids (56 * cap0) HAR HLED HKD) as (Hkd4 & _ & Hkdc & _).
  lazymatch type of HS2 with st_ok_pi _ _ ?E' ?ssF (restrict _ ?msF) =>
    pose proof (pl_fin_regs (w_H W) E' ssF msF regs regs2 x kids HS2
      ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
      ltac:(intros r Hr; unfold pg_all in Hr; cbn [map In] in Hr;
            repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr)
      R2' ltac:(lia) RK2) as KF;
    pose proof (st_ok_pi_restrict_reg (w_H W) E' ssF msF 10%bv HS2) as G10;
    lazymatch type of G10 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in G10 end;
    assert (G10v : getr (ms_regs msF) 10%bv = w64 (kids + 56 * Z.of_nat i));
    [ rewrite G10, (denot_lit_U E'), (gs_U_hit E' 21 42 (Z.of_nat i) kids); [reflexivity | | | exact (proj1 Hkids) | lia];
      [ rewrite ew_ewset_other by lia; rewrite (FR 21%nat 21%bv) by (lia || reflexivity); rewrite QL by (cbn; tauto); exact R21
      | rewrite ew_ewset_other by lia; rewrite (FXa2 42%nat) by lia; unfold xs; cbn [nth app map Nat.sub]; reflexivity ]
    | ] end.
  (* the tree at the exit's memory, mem2 *)
  assert (KFm : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) by exact KM2.
  pose proof (NODEK mem2 KFm) as HnF. pose proof HnF as HnF'. cbn [pj_nodeR] in HnF'.
  destruct HnF' as (_ & _ & numF & strF & kidsF & keysF & nF & capF & HhF & EsF & EnF & HcnF & HcapF & DiF & EDF & HmF).
  pose proof HhF as (_ & _ & _ & _ & (HkF0 & HkF) & _).
  pose proof (gs_val8_uniq _ _ _ _ HkF Hk2 HkF0 (proj1 Hkids)) as EkF. subst kidsF strF.
  eapply (pg_fin ly S Hp W regs mem md o (JObj members) D kname Lam peak cnt fail ran most own _ _ _ _ _ (kids + 56 * Z.of_nat i)
    HAR HLED HJ2 HPM).
  + intros a Ha. rewrite EMf. apply KM2; lia.
  + exact Hra.
  + intros r Hr. apply KF. right. exact Hr.
  + apply KF. left. reflexivity.
  + exact G10v.
  + right. split; [exact Hon|]. rewrite EMf. split; [exact HnF|].
    exact (pjs_res_found (PA := PA) (mrestrict (w_H W) mem2) (prh_lin Lam) o members D kname numF kids keysF nF capF DiF i u
      HhF EDF HmF Ei Hpre).
- (* not found: the member's name is not kname *)
  rewrite branch_eq_U, U_SLit, U10 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
  pose proof Hxs' as (_ & _ & _ & _ & Hxg').
  pose proof HKT as ((Hkg' & _) & _).
  assert (Hne : nm <> kname).
  { intros Enm. apply Hc. rewrite (proj2 Hiff (proj2 (pjs_strcmp_iff W (ms_mem ms) x nm k kname Hxg' Hkg') Enm)). reflexivity. }
  assert (Hpre' : forall j' nm' u', (j' < Datatypes.S i)%nat -> nth_error members j' = Some (nm', u') -> nm' <> kname).
  { intros j' nm' u' Hj' Ej'. destruct (Nat.eq_dec j' i) as [-> | Hji].
    - rewrite Ei in Ej'. injection Ej' as <- <-. exact Hne.
    - apply (Hpre j' nm' u'); [lia | exact Ej']. }
  (* slots 46 .. 51: s5 -= 56, s4 -= 1, s2 += 8, s7 += 1, s6 += 8, bnez s4 *)
  paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM PG_Bspan; [gs_awr0|].
  gs_memeq HF EMn. clear HF HG HFr.
  (* s4 after the decrement: n - (i + 1) *)
  assert (U20 : U E2 (SOff 20 (-1)) = Z.of_nat (length members) - Z.of_nat i - 1).
  { rewrite U_SOff, (FR 20%nat 20%bv) by (lia || reflexivity). rewrite QL by (cbn; tauto). rewrite R20.
    rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
  (* the values the loop head sees next, from the branch state's registers *)
  assert (GV : forall n (r : bv 5) c wv, (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
    In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr regsL r = Z_to_bv 64 wv -> sv_denot E2 (SOff n c) = Z_to_bv 64 (wv + c)).
  { intros n r c wv Hn Hr Hin Hw. apply gs_denot_off. rewrite (FR n r Hn Hr), (QL r Hin). exact Hw. }
  clear Hc. psrr_branch_tok RUN BR HS2 SHOK2 PG_Bspan.
  + (* members left: back to the loop head with i + 1 *)
    rewrite branch_ne_U, U_SLit, U20 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK2 HPM PG_Bspan (AF_pg + 160).
    all: try gs_awr0.
    gs_memeq HF EMn2. clear HF HG HFr.
    lazymatch type of HS2 with st_ok_pi _ _ ?E' ?ssq (restrict _ ?msq) =>
      pose proof (st_ok_pi_restrict_mkst (w_H W) E' ssq msq HS2 eq_refl) as Hmk2;
      pose proof (fun r => st_ok_pi_restrict_reg (w_H W) E' ssq msq r HS2) as GR;
      rewrite Hmk2; replace (ss_pc ssq) with (AF_pg + 160) by (vm_compute; reflexivity) end.
    assert (Hlt : (Datatypes.S i < length members)%nat) by lia.
    eapply (IH (length members - Datatypes.S i)%nat ltac:(lia) (Datatypes.S i) _ _ _ _ eq_refl Hlt HJ2 HPM).
    * intros a Ha Hw. rewrite EMn2, EMn. exact (KM2 a Ha Hw).
    * intros off r Hin. rewrite EMn2, EMn. exact (HFW2 off r Hin).
    * gr GR. rewrite (GV 2%nat 2%bv 0 (spZ regs - 80) ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R2); f_equal; lia.
    * gr GR. rewrite (GV 8%nat 8%bv 0 o ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R8); unfold w64; f_equal; lia.
    * gr GR. rewrite (GV 9%nat 9%bv 0 k ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R9); unfold w64; f_equal; lia.
    * gr GR. rewrite (GV 19%nat 19%bv 0 SHADOW_OFF ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R19); f_equal; lia.
    * gr GR. rewrite (GV 20%nat 20%bv (-1) (Z.of_nat (length members) - Z.of_nat i) ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R20);
      f_equal; lia.
    * gr GR. rewrite (GV 21%nat 21%bv (-56) (-56 * Z.of_nat i) ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R21); f_equal; lia.
    * gr GR. rewrite (GV 22%nat 22%bv 8 sl ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R22); f_equal; subst sl; lia.
    * gr GR. rewrite (GV 18%nat 18%bv 8 sl ltac:(lia) ltac:(reflexivity) ltac:(cbn; tauto) R18); f_equal; subst sl; lia.
    * gr GR. rewrite (gs_denot_off E2 23 (SHADOW_OFF + sl / 8) 1); [f_equal; subst sl; lia|].
      rewrite (FR 23%nat 23%bv) by (lia || reflexivity). exact Q23.
    * intros r Hr. rewrite GR. pose proof Hr as Hr0. cbn [map In] in Hr0.
      repeat (destruct Hr0 as [<- | Hr0];
        [ lazymatch goal with |- sv_denot _ ?e = getr _ ?rr =>
            let e' := eval vm_compute in e in change e with e';
            let z := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
            rewrite (gs_denot_off E2 z (bv_unsigned (getr regs rr)) 0);
            [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | rewrite (FR z rr ltac:(lia) ltac:(vm_compute; reflexivity)), (RK2 rr Hr); symmetry; apply Z_to_bv_bv_unsigned ] end |]).
      destruct Hr0.
    * exact Hpre'.
  + (* the last member: a0 = 0, the nine registers back, ret *)
    rewrite branch_ne_U, U_SLit, U20 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM PG_Bspan; [gs_awr0|].
    gs_memeq HF EMf. clear HF HG HFr.
    eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS2 with st_ok_pi _ _ ?E' ?ssF (restrict _ ?msF) =>
      pose proof (pl_fin_regs (w_H W) E' ssF msF regs regs2 x kids HS2
        ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
        ltac:(intros r Hr; unfold pg_all in Hr; cbn [map In] in Hr;
              repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr)
        R2' ltac:(lia) RK2) as KF;
      pose proof (st_ok_pi_restrict_reg (w_H W) E' ssF msF 10%bv HS2) as G10;
      lazymatch type of G10 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in G10 end end.
    eapply (pg_fin ly S Hp W regs mem md o (JObj members) D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ2 HPM).
    * intros a Ha. rewrite EMf, EMn. apply KM2; lia.
    * exact Hra.
    * intros r Hr. apply KF. right. exact Hr.
    * apply KF. left. reflexivity.
    * rewrite G10. reflexivity.
    * right. split; [exact Hon|]. rewrite EMf, EMn. split; [exact (NODEK mem2 KM2)|].
      apply pjs_res_none. intros j' nm' u' Hj' Ej'. apply (Hpre' j' nm' u'); [lia | exact Ej'].
Qed.

Theorem pj_get_holds_P : tpj_get_specXP (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK Pm.
Proof.
unfold tpj_get_specXP.
intros ly S Hp W regs mem md ch o k kname t D Lam peak cnt fail ran most own [HPRE [HROD [HTOP [HRAZ HFRM]]]] H10 H11 HO HK HLED.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pg_frame as FS. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlo : YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_A)) by lia.
(* the node's header words, when there is a node (atoms 33 .. 36) *)
assert (HHD : exists ty kids keys nn, o <> 0 -> exists num str cap,
  pj_hdrR SEGS (mrestrict (w_H W) mem) o ty num str kids keys nn cap /\ ty = tag t).
{ destruct HO as [Ho0 | (Hnode & _)]; [exists 0, 0, 0, 0; intros H; contradiction|].
  destruct (gs_node_hdr _ _ _ _ _ Hnode) as (num & str & kids & keys & nn & cap & Hh).
  exists (tag t), kids, keys, nn. intros _. exists num, str, cap. split; [exact Hh | reflexivity]. }
destruct HHD as (ty & kids & keys & nn & HHD).
set (xs := [ty; kids; keys; nn]).
destruct (pg_entry ly S Hp W regs mem md ch xs HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
assert (HPM : Pm mem -> Pm mem) by (intros h; exact h).
remember (pg_E regs xs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pg_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold pg_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E)
  by (rewrite HE; split; [intros n Hn; unfold pg_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_pg)) with (Z_to_bv 64 (BASE + AF_pg)).
(* ---- slots 0-10: the frame, the nine saves, beqz a0 ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan; [gs_awr regs Usp|].
gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KO0. clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK PG_Bspan.
- (* o = 0: the nine registers back, ret with a0 = o = 0 *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. rewrite U_SOff, E10, H10, Z.add_0_r in Hc. unfold w64 in Hc.
  assert (Ho0 : o = 0).
  { destruct HO as [Ho0 | (_ & Hrs)]; [exact Ho0|]. destruct Hrs as (H4096 & _ & Hamr & _).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
    rewrite unsigned_lit_small, zcanon_id in Hc by (unfold M64; lia). lia. }
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan; [gs_awr regs Usp|].
  gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KO1. clear HF HG HFr.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ (1%bv :: 10%bv :: pg_all) HS HAE ltac:(vm_compute; reflexivity)) as KK.
  eapply (pg_fin ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ HPM).
  + intros a Ha. rewrite KO1, KO0 by lia. reflexivity.
  + exact Hra.
  + intros r Hr. apply KK. right; right; exact Hr.
  + apply KK. left; reflexivity.
  + transitivity (getr regs 10%bv); [exact (KK 10%bv ltac:(right; left; reflexivity)) | rewrite H10, Ho0; reflexivity].
  + left. split; [exact Ho0 | reflexivity].
- (* o <> 0: the node *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc. rewrite U_SOff, E10, H10, Z.add_0_r in Hc. unfold w64 in Hc.
  assert (Hon : o <> 0) by (intros ->; apply Hc; reflexivity).
  destruct HO as [Ho0 | (Hnode & Hrs)]; [contradiction|].
  destruct (HHD Hon) as (num & str & cap & Hh & Ety).
  pose proof Hrs as (H4096 & Hplace & Hamr & Hwin & HRA & HHU).
  assert (Ho47 : o + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  pose proof (pg_foot ly S Hp W mem md regs o t D Lam peak cnt fail ran most own HAR HLED Hlo Hnode Hrs) as HFT.
  assert (KR : forall x, pj_footR o D x -> mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
  { intros x Hx. destruct (HFT x Hx) as (Hr & Hn & Hw). exact (gs_raw_of_aview _ _ mem (ms_mem ms) x Hr Hn (KO0 x Hr Hw)). }
  assert (Hh1 : pj_hdrR SEGS (mrestrict (w_H W) (ms_mem ms)) o ty num str kids keys nn cap).
  { apply (pj_hdrR_frame SEGS _ _ o ty num str kids keys nn cap Hh). apply gs_agree. intros x Hx. apply KR. left. exact Hx. }
  assert (HRA1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF o 56).
  { eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KO0; lia. }
  destruct Hh1 as ((Hal8 & _) & (Hty0 & Hty) & _ & _ & (Hk0 & Hk) & (Hy0 & Hy) & (Hn0 & Hn) & _).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew E 33 = Z_to_bv 64 ty)
    by (rewrite EL by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = Z_to_bv 64 kids)
    by (rewrite EL by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E35 : ew E 35 = Z_to_bv 64 keys)
    by (rewrite EL by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E36 : ew E 36 = Z_to_bv 64 nn)
    by (rewrite EL by (unfold A_TEXT; lia); change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Uo : base_val E (Some 10%nat) = o)
    by (cbn [base_val]; rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
  (* the node is apart from the frame (outside the stack window) and from the GOT word and the cell (image bytes) *)
  assert (Dfr : o + 56 <= spZ regs - 80 \/ spZ regs <= o).
  { destruct (Z_le_gt_dec (o + 56) (spZ regs - 80)); [left; lia|]. destruct (Z_le_gt_dec (spZ regs) o); [right; lia|].
    exfalso. destruct (Z_le_gt_dec o (spZ regs - 80)); [apply (Hwin (spZ regs - 80)) | apply (Hwin o)]; lia. }
  assert (Dimg : forall g, (forall i, 0 <= i < 8 -> in_img SEGS (g + i)) -> o + 56 <= g \/ g + 8 <= o).
  { intros g Hg. destruct (Z_le_gt_dec (o + 56) g); [left; lia|]. destruct (Z_le_gt_dec (g + 8) o); [right; lia|].
    exfalso. destruct (Z_le_gt_dec o g).
    - assert (Hf : pj_footR o D g) by (unfold pj_footR; left; lia).
      destruct (HFT g Hf) as (_ & Hn' & _). apply Hn'. replace g with (g + 0) by lia. apply Hg. lia.
    - assert (Hf : pj_footR o D o) by (unfold pj_footR; left; lia).
      destruct (HFT o Hf) as (_ & Hn' & _). apply Hn'. replace o with (g + (o - g)) by lia. apply Hg. lia. }
  pose proof (Dimg (VAL (A_OBJ 0)) (fun i Hi => proj1 (Hobj i Hi))) as Dgot.
  pose proof (Dimg (VAL (A_OBJ 12)) (fun i Hi => proj2 (Hobj i Hi))) as Dcell.
  assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
    by (subst E; unfold pg_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
    by (subst E; unfold pg_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
    pose proof (st_ok_pi_add_region (PI := PA) E ssq _ pg_node HS ltac:(vm_compute; reflexivity)) as HSN end.
  lazymatch type of HSN with ?P -> ?Q -> _ => assert (HRN : P); [|assert (HDN : Q); [|specialize (HSN HRN HDN)]] end.
  { unfold region_ok, pg_node. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
    rewrite Uo. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS E _ o 0 4 (SOff 33 0) ty); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      rewrite Z.add_0_r. exact Hty.
    - apply (chunk_ok_val SEGS E _ o 24 8 (SOff 34 0) kids); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hk].
    - apply (chunk_ok_val SEGS E _ o 32 8 (SOff 35 0) keys); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hy].
    - apply (chunk_ok_val SEGS E _ o 40 8 (SOff 36 0) nn); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hn]. }
  { apply all_disjoint_of_extents. unfold pg_node, extent_of_region. cbn [ss_mem add_cond map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite Uo. cbn [base_val]. rewrite Usp.
    match goal with |- context [ew E ?g0] => lazymatch eval vm_compute in (Nat.eqb g0 (A_OBJ 0)) with true =>
      change (ew E g0) with (ew E (A_OBJ 0)) end end.
    match goal with |- context [ew E ?g1] => lazymatch eval vm_compute in (Nat.eqb g1 (A_OBJ 12)) with true =>
      change (ew E g1) with (ew E (A_OBJ 12)) end end.
    rewrite Eo0, Eo12, !unsigned_lit_small by lia.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
  clear HS HRN HDN. rename HSN into HS.
  (* the node pointer's range and alignment, for the token engine's shadow checks *)
  pose proof (st_ok_pi_add_fact (PI := PA) E _ _ 10%nat (mkAF 4096 (2 ^ 47 - 56) 3) HS) as HSF.
  lazymatch type of HSF with ?P -> _ => assert (HAF : P); [|specialize (HSF HAF); clear HS HAF; rename HSF into HS] end.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, H10. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 3) with 8. repeat split; lia. }
  (* ---- slots 11-22: s1, s0, the shadow base, the node's type, bne type 6 ---- *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan.
  all: try (gs_awr_any regs Usp).
  all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
    cbn [ms_mem]; unfold PG_Bx; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
    rewrite ?E32, ?E10, ?H10; unfold w64;
    rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
    lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
      change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
    eapply range_addressable_sub; [exact HRA1 | lia | lia]).
  gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KO1. clear HF HG HFr.
  rewrite Ety in E33.
  (* the post at any exit after the node seat: the node kept at the exit memory *)
  assert (NODEK : forall memF, (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
      aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
    pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o t D).
  { intros memF KF. apply (gs_node_kept W mem memF _ o t D Hnode). intros x Hx.
    destruct (HFT x Hx) as (Hr & Hni & Hw). split; [exact Hr|]. split; [exact Hni|]. exact (KF x Hr Hw). }
  clear Hc. psrr_branch_tok RUN BR HS SHOK PG_Bspan.
  + (* taken: not an object; a0 = 0, the nine registers back, ret *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc t E33. rewrite U_SLit in Hc.
    rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan; [gs_awr_any regs Usp|].
    gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KO2. clear HF HG HFr.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
      assert (HAE' : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E')
        by (eapply env_agree_trans; [exact HAE | split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E' _ _ regs _ (1%bv :: pg_all) HS HAE' ltac:(vm_compute; reflexivity)) as KK;
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
        by (intros a Ha Hw; rewrite KO2, KO1, KO0 by assumption; reflexivity) end.
    prreg HS (10%bv : bv 5) G10.
    eapply (pg_fin ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ HPM).
    * intros a Ha. apply KF; lia.
    * exact Hra.
    * intros r Hr. apply KK. right; exact Hr.
    * apply KK. left; reflexivity.
    * rewrite G10. reflexivity.
    * right. split; [exact Hon|]. split; [exact (NODEK _ KF)|].
      destruct t; cbn [prhPj_get_res]; try reflexivity. exfalso. apply Hc. reflexivity.
  + (* not taken: an object *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc t E33. rewrite U_SLit in Hc.
    rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (gs_tag6 t Hc) as (members & ->).
    (* the header words of the object, as the tree states them *)
    pose proof Hnode as Hnode'. cbn [pj_nodeR] in Hnode'.
    destruct Hnode' as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hhdr0 & Es0 & En0 & Hcn0 & Hcap0 & Di & ED & Hmems).
    pose proof Hh as (_ & _ & _ & _ & (Hk0e & Hke) & (Hy0e & Hye) & (Hn0e & Hne) & _).
    pose proof Hhdr0 as (_ & _ & _ & _ & (Hk0' & Hk') & (Hy0' & Hy') & (Hn0' & Hn') & _).
    pose proof (gs_val8_uniq _ _ _ _ Hke Hk' Hk0e Hk0') as Ekids. subst kids0.
    pose proof (gs_val8_uniq _ _ _ _ Hye Hy' Hy0e Hy0') as Ekeys. subst keys0.
    pose proof (gs_val8_uniq _ _ _ _ Hne Hn' Hn0e Hn0') as Enn. subst n0.
    (* the views of the current memory outside the window, against the entry's *)
    assert (HRAK : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
        aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) -> range_addressable (aview SEGS (w_H W) m') SHADOW_OFF o 56).
    { intros m' KF. eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KF; lia. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msq) =>
      assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem msq) a = aview SEGS (w_H W) mem a)
        by (intros a Ha Hw; rewrite KO1, KO0 by assumption; reflexivity) end.
    clear KO0 KO1.
    (* ---- slots 23-29: n = node[40], beqz n ---- *)
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan.
    all: try (gs_awr_any regs Usp).
    all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
      cbn [ms_mem]; unfold PG_Bx; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
      rewrite ?E32, ?E10, ?H10; unfold w64;
      rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
      lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
        change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
      eapply range_addressable_sub; [apply HRAK; exact KC | lia | lia]).
    gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KN. clear HF HG HFr.
    lazymatch type of KN with forall a, _ -> _ -> aview _ _ ?m' a = _ =>
      assert (KC' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
        aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
    clear KN KC. rename KC' into KC.
    assert (E36' : U (ewset (ewset (ewset E 512 w) 513 w0) 512 w1) (SOff 36 0) = nn)
      by (rewrite U_SOff; rewrite ?ew_ewset_other by lia; rewrite E36, Z.add_0_r, unsigned_lit_small, zcanon_id by (unfold M64; lia); reflexivity).
    clear Hc. psrr_branch_tok RUN BR HS SHOK PG_Bspan.
    * (* n = 0: no member; a0 = 0, the nine registers back, ret *)
      rewrite branch_eq_U, U_SLit, E36' in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc.
      assert (Hm0 : members = []) by (destruct members; [reflexivity | cbn [length] in Enn; lia]). subst members.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan; [gs_awr_any regs Usp|].
      gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KN. clear HF HG HFr.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
      lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
        assert (HAE' : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E')
          by (eapply env_agree_trans; [exact HAE | split; [intros n' Hn''; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
        pose proof (regs_kept_of_st_ok_pi (PI := PA) E' _ _ regs _ (1%bv :: pg_all) HS HAE' ltac:(vm_compute; reflexivity)) as KK;
        assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
          by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
      prreg HS (10%bv : bv 5) G10.
      eapply (pg_fin ly S Hp W regs mem md o (JObj []) D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ HPM).
      -- intros a Ha. apply KF; lia.
      -- exact Hra.
      -- intros r Hr. apply KK. right; exact Hr.
      -- apply KK. left; reflexivity.
      -- rewrite G10. reflexivity.
      -- right. split; [exact Hon|]. split; [exact (NODEK _ KF)|].
         cbn [prhPj_get_res]. left. split; [intros nm u Hin; destruct Hin | reflexivity].
    * (* n <> 0: the keys word, s5 = 0, s6 = keys, s7 = its shadow, to the loop head *)
      rewrite branch_eq_U, U_SLit, E36' in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_Bspan.
      all: try (gs_awr_any regs Usp).
      all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
        cbn [ms_mem]; unfold PG_Bx; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
        rewrite ?E32, ?E10, ?H10; unfold w64;
        rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
        lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
          change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
        eapply range_addressable_sub; [apply HRAK; exact KC | lia | lia]).
      gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_A)) (spZ regs) KN. clear HF HG HFr.
      lazymatch type of KN with forall a, _ -> _ -> aview _ _ ?m' a = _ =>
        assert (KC' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_A) <= a < spZ regs) ->
          aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
      clear KN KC. rename KC' into KC.
      assert (Hlen0 : (0 < length members)%nat) by (destruct members; [cbn [length] in Enn; lia | cbn; lia]).
      assert (Hcp : 0 < cap0) by lia.
      destruct Hcap0 as [(Hc00 & _) | (_ & HKD & HKY)]; [lia|].
      (* the loop head's registers and frame words *)
      lazymatch type of HS with st_ok_pi _ _ ?E' ?ssq (restrict _ ?msq) =>
        pose proof (st_ok_pi_restrict_mkst (PI := PA) (w_H W) E' ssq msq HS eq_refl) as Hmk;
        set (EQ := E') in HS; set (MQ := msq) in * end.
      assert (Q2 : forall nq, (nq < 512)%nat -> ew EQ nq = ew E nq) by (intros nq Hnq; subst EQ; rewrite ?ew_ewset_other by lia; reflexivity).
      assert (QR : forall r : bv 5, ew EQ (Z.to_nat (bv_unsigned r)) = getr regs r).
      { intros r. pose proof (bv_unsigned_in_range 5 r) as Hr5. unfold bv_modulus in Hr5. change (2 ^ Z.of_N 5) with 32 in Hr5.
        assert (Hr32 : (Z.to_nat (bv_unsigned r) < 32)%nat) by lia.
        rewrite Q2 by lia. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
      assert (Usp' : bv_unsigned (ew EQ 2) = spZ regs) by (rewrite Q2 by lia; exact Usp).
      prreg HS (2%bv : bv 5) G2. prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9.
      prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
      prreg HS (21%bv : bv 5) G21. prreg HS (22%bv : bv 5) G22.
      pose proof (st_ok_pi_restrict_reg (PI := PA) (w_H W) EQ _ MQ 23%bv HS) as G23.
      lazymatch type of G23 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in G23 end.
      assert (E35Q : ew EQ 35 = Z_to_bv 64 keys) by (rewrite Q2 by lia; exact E35).
      assert (E32Q : ew EQ 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite Q2 by lia; exact E32).
      assert (Hkeysb : 4096 <= keys /\ keys + 8 * cap0 <= YM05.alloc_ceiling /\ keys mod 16 = 0).
      { destruct (pg_lam_low ly S Hp W mem md Lam peak cnt fail ran most own keys (8 * cap0) HAR HLED HKY) as (H4q & _ & Hcq & Habq & _).
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Habq) as (Halq & _). split; [lia|]. split; [lia|]. lia. }
      (* the frame words *)
      lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
        pose proof (st_ok_region_nth SEGS EQ (abs_ss VAL ssq) _ 1 (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
          [YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
           YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
           YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
           YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
           YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS eq_refl) as RGF end.
      assert (HFW : forall off r, In (off, r) pg_saves ->
        val_mem SEGS (mrestrict (w_H W) (ms_mem MQ)) (spZ regs - 80 + off) 8 (bv_unsigned (getr regs r))).
      { intros off r Hin. pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr64.
        assert (HIN : In (YP09.mkChunk (off - 80) (CVal 8 (SOff (Z.to_nat (bv_unsigned r)) 0)))
          [YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
           YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
           YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
           YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
           YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]).
        { unfold pg_saves in Hin. cbn in Hin.
          repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; cbn; tauto|]). destruct Hin. }
        pose proof (slot_of_region SEGS EQ _ (spZ regs) _ _ _ _ _ (off - 80) _ (bv_unsigned (getr regs r)) RGF Usp' HIN) as V.
        replace (spZ regs - 80 + off) with (spZ regs + (off - 80)) by lia. apply V; [|exact Hr64].
        cbn [sv_denot]. rewrite QR, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      (* the loop head, with no member done *)
      assert (HAEQ : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) EQ)
        by (eapply env_agree_trans; [exact HAE | split; [intros nq Hnq; apply Q2; lia | reflexivity]]).
      pose proof (regs_kept_of_st_ok_pi (PI := PA) EQ _ _ regs _ (map (Z_to_bv 5) [3; 4; 24; 25; 26; 27]) HS HAEQ
        ltac:(vm_compute; reflexivity)) as KK.
      assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
      rewrite Hmk.
      lazymatch goal with |- context [BASE + ss_pc ?ssq] => replace (ss_pc ssq) with (AF_pg + 160) by (vm_compute; reflexivity) end.
      eapply (pg_loop ly S Hp W regs mem md o k kname members D Lam peak cnt fail ran most own kids keys cap0 Di
        HAR HLED Hra ltac:(lia) Hal16 Hlo Hgp Htp Hon Hnode Hrs (conj Hk0e Hke) (conj Hy0e Hye) ltac:(lia) HKD HKY
        ltac:(rewrite ED; intros b Hb; apply in_or_app; right; exact Hb) Hmems HK HROD (length members) 0
        (ms_regs MQ) (ms_mem MQ) _ _ ltac:(lia) Hlen0 HJ HPM KC HFW).
      -- rewrite G2, Usp'; f_equal; lia.
      -- rewrite G8, Q2 by lia. rewrite E10. exact H10.
      -- rewrite G9, Q2 by lia. rewrite E11. exact H11.
      -- rewrite G19. exact E32Q.
      -- rewrite G20, Q2, E36 by lia; f_equal; lia.
      -- rewrite G21. reflexivity.
      -- rewrite G22, E35Q; f_equal; lia.
      -- rewrite G18, E35Q; f_equal; lia.
      -- rewrite G23, (denot_lit_U EQ), (gs_U_shadow_of EQ 32 35 SHADOW_OFF keys E32Q E35Q) by (unfold SHADOW_OFF; lia).
         f_equal; lia.
      -- intros r Hr. apply KK. exact Hr.
      -- intros j' nm u Hj'. lia.
Qed.

End p.

(* The m-form text: the walk at the invariant YAkMemnorm.memnorm *)
Theorem pj_get_holds : tpj_get_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK.
Proof.
apply (tpj_get_specX_of_P (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK).
exact (pj_get_holds_P (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) (fun m m' H => H)).
Qed.

End f.
End d.

Print Assumptions pj_get_holds_P.
Print Assumptions pj_get_holds.
Set Printing All.
Check pj_get_holds_P.
Check pj_get_holds.
Unset Printing All.
