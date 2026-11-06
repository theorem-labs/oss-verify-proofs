(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the HEAD HALF of the image-B (fuzz_reply.asan-ubsan) TOP segment of
   fuzz_reply's drain and the composed TOP.  TOP (lib/B/W_drain_cx.v dr_top_stmt, DI 0x833c0 -> DI / DEND / DRB 0)
   is split at B's slot-found point 0x83524 (lib/B/W_drain_topb_cx.v A_dr_slot, a Theorem Labs lane, FROZEN):
     head  DI 0x833c0 -> DT2 0x83524 at the grown state dgrow s1: the round's growth (cap - used < 4096 tested
           as `(cap - used) >> 12 != 0` at 0x833e4; realloc #1 at 0x83410 through arealloc_cf_rule, whose forced
           success refutes the failure arm `beqz a0 -> 0x83fa8`), then source_of's scan over g_s 0x83498 ..
           0x834cc, which finds slot j at the `beq a1,a4` of 0x834c0 (the not-found exit 0x834d0 is refuted from
           DMEM's asrc_at at dHA (open = 1, fd = hs_fd) with DSAME / DBASE's hs_fd = re_fd, and aothers_at for the
           slots before j);
     tail  DT2 -> DI (EINTR) / DEND / DRB 0, a Theorem Labs lane's dr_toptail_stmt.
   0x83524 is reached only from that beq (0x83520 is `j 0x83574`), and between 0x833c0 and 0x83524 the code writes
   only s3, s7, a0-a6 and (at realloc) ra, so DI's dregs_top holds at the seam unchanged.
   dr_top_of composes the two halves: the tail's EINTR continuation at dclr sg is dr_top_stmt's at
   dclr (dgrow s1), because ds_eintr (dgrow s1) reduces to ds_eintr s1. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_tophead.v, with its module paths and module names changed; 2374 of its 2506 lines of code are new or changed and 4077 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, read_members on the #102 pins, image A' (asan, bin/fuzz_preset/fuzz_preset.asan
   sha256 1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, the #102 pin A' of the pau-preset-102
   SHA256SUMS): the walk of read_members (entry
   pa_sigma AS_read_members, 158 slots of lib/A/Listing_prog.v) against the text tread_members_specX
   (lib/A/PRH_FnCheck.v of the #102 kit of record decff67d721f).
   PIN SHAS: proof base ed6e9a1a2e98 (the kit tip at the brief); kit of record decff67d721f; listing v3
   lib/A/Listing_prog.v 7ed1529926bd and lib/A/PAImg_prog.v 505a51ff7d08 (commit
   74dcda1eda12); the text blob lib/A/PRH_FnCheck.v 4cb899514e6c; callee texts lib/A/PRH_FnPj.v a21e5a5cb897.
   PARAMETRIC over {PA : PAImg A_prog_listing} (owner's rule, 12:48Z): at the concrete PI_prog_A the kernel's
   Qed of even the entry seat does not finish (it re-checks conversions against the 7264-slot table); the image
   facts are the Section's Hent / Hobj_lo / PAB / PAH / Hlits / Htop_ptr / Hpst_ro, each decided at PI_prog_A by
   vm_compute in the instance file.
   STATE: read_members_holds is Qed. rm_body walks the entry, pj_get (doc, "params") and (doc, "state") to the
   six-key loop head (AF_rm + 140); then segment lemmas, each from a re-seat over concrete facts: rm_top_loop (the
   six keys of `top`, induction on the keys left), rm_mid (pj_get (doc, "plugin"), pj_get_str (its member, "id"),
   the NULL test of params), rm_pentry (params' type check), rm_ploop (the params loop, induction on the items left:
   pj_get_str (kids + 56 i, "symbol"), pj_get (kids + 56 i, "value")), rm_tail (pj_get_str (state, "encoding") /
   (state, "bytes"), the epilogue). The instance at PI_prog_A is lib/A/Prog/read_members_inst.v.
   NAMED PREMISES: PJ_GET / PJ_GET_STR are the texts verbatim; RM_IMG holds the thirteen key literals and the `top`
   table as facts about B; HW is the prh_head_wide. LAWS is AR_laws_x at hl = cf_head, so the former gap premise RM_G3
   is gone: its user-bytes half is LAWS' field 14 (alx_hshadow), its head-poison half LAWS' field 22 (alx_hhead, used
   through YCbqG's hhead_not_addressable_x). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition rm_keys : list (Z * Z) :=
  map (fun on => (pa_val (A_OBJ 2) + fst on, snd on))
    [(0x11020, 6); (0x11040, 2); (0x11060, 4); (0x11080, 7); (0x110a0, 9); (0x110c0, 10); (0x110e0, 6);
     (0x11100, 5); (0x11120, 6); (0x11140, 6); (0x11160, 5); (0x11180, 8); (0x111a0, 5)].
End k.

(* read_members' offset in the listing (DERIVED: its slot times 4, PAImg_prog A_entry_read_members) *)
Definition AF_rm : Z := 4 * Z.of_nat (A_prog_slot AS_read_members).
(* the shadow base atom (an extra env slot, 32) and the span the token engine checks it against *)
Definition RM_Bx : sv := SOff 32 0.
Definition RM_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the entry seat: the own frame of 128 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell *)
Definition rm_regions : smem := [stack_region 128; got_regionP; bcell_regionP 32].
Definition rm_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_rm : sstate := mkSS AF_rm sr_atoms rm_regions None rm_facts.

(* ---- the re-seats (the four segment lemmas below start from concrete facts, as a Theorem Labs lane's pj_get loop does) ---- *)
(* the thirteen registers the prologue saves, at their offsets from the frame base (sp after the prologue) *)
Definition rm_saves : list (Z * bv 5) :=
  [(120, 1%bv); (112, 8%bv); (104, 9%bv); (96, 18%bv); (88, 19%bv); (80, 20%bv); (72, 21%bv); (64, 22%bv);
   (56, 23%bv); (48, 24%bv); (40, 25%bv); (32, 26%bv); (24, 27%bv)].
(* a seat's frame region: sp is atom 2, the saved registers are atoms 33 .. 45 (rm_saves' order), plus extra chunks;
   the code writes only sp + 8 (the spill of params' granule bound) and sp + 16 (seen) after the prologue *)
Definition rm_frame (xc : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 128 8 24
    (xc ++ [YP09.mkChunk 120 (CVal 8 (SOff 33 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0));
      YP09.mkChunk 104 (CVal 8 (SOff 35 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SOff 37 0));
      YP09.mkChunk 80 (CVal 8 (SOff 38 0)); YP09.mkChunk 72 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
      YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 48 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 8 (SOff 43 0));
      YP09.mkChunk 32 (CVal 8 (SOff 44 0)); YP09.mkChunk 24 (CVal 8 (SOff 45 0))]).
(* a seat's facts: sp (atom 2) and the shadow base (atom 32), plus extra atom facts *)
Definition rm_sfacts (xf : list (nat * afact)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: xf) [] [].
(* the tail seat (AF_rm + 456, the pj_get_str (state, "encoding") call's set-up): s0 the state member (atom 8), the
   frame's seen word (atom 46) *)
Definition ss_tail : sstate := mkSS (AF_rm + 456) sr_atoms [rm_frame [YP09.mkChunk 16 (CVal 8 (SOff 46 0))]] None (rm_sfacts []).
(* the params loop seat (AF_rm + 328, the loop head): s1 = params (atom 9), s2 / s3 its kids / n words, s6 / s10 / s11
   the shadow bytes of its type / n / kids words, s7 = 5 (JArr's tag); the node's type, kids (atom 48) and n (atom 47)
   words; the frame's seen word (atom 46) *)
Definition rm_node : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit 5)); YP09.mkChunk 24 (CVal 8 (SOff 48 0)); YP09.mkChunk 40 (CVal 8 (SOff 47 0))].
Definition rm_lregs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 9 24)) 19%bv (SOff 9 40))
    22%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 9 0) (SLit 3)))) 23%bv (SLit 5))
    26%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 9 40) (SLit 3))))
    27%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 9 24) (SLit 3))).
Definition ss_loop : sstate :=
  mkSS (AF_rm + 328) rm_lregs [rm_frame [YP09.mkChunk 16 (CVal 8 (SOff 46 0))]; rm_node] None
    (rm_sfacts [(9%nat, mkAF 4096 (2 ^ 47 - 56) 3)]).
(* the shadow the token engine reads for params' words: its whole node *)
Definition RM_SHN : list shent := [mkSHE 9 0 56].
(* the seat at params' type check (AF_rm + 240, after its NULL test): s4 the shadow base (atom 32's value), s1 = params
   (atom 9), its type word (atom 47), the frame's seen word (atom 46) *)
Definition rm_pnode : YP09.region := YP09.mkRegion (Some 9%nat) 0 56 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 47 0))].
Definition ss_pentry : sstate :=
  mkSS (AF_rm + 240) (sr_set sr_atoms 20%bv (SOff 32 0)) [rm_frame [YP09.mkChunk 16 (CVal 8 (SOff 46 0))]; rm_pnode] None
    (rm_sfacts [(9%nat, mkAF 4096 (2 ^ 47 - 56) 3)]).
(* the seat after the six keys (AF_rm + 192): s2 = doc (atom 18), s4 the shadow base (atom 32's value), s1 = params
   (atom 9), s0 = state (atom 8), the frame's seen word (atom 46) *)
Definition ss_mid : sstate :=
  mkSS (AF_rm + 192) (sr_set sr_atoms 20%bv (SOff 32 0)) [rm_frame [YP09.mkChunk 16 (CVal 8 (SOff 46 0))]] None (rm_sfacts []).
(* the six-key loop seat (AF_rm + 140, the loop head): s5 the table cell top + 8 i (atom 21), s6 its shadow byte's
   address, s7 = -48, s3 = -8 i (atom 19); the cell holds the key's address (atom 47); the frame's seen word (atom 46) *)
Definition rm_tcell : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 47 0))].
Definition ss_top : sstate :=
  mkSS (AF_rm + 140)
    (sr_set (sr_set sr_atoms 22%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 21 0) (SLit 3)))) 23%bv
      (SLit 18446744073709551568))
    [rm_frame [YP09.mkChunk 16 (CVal 8 (SOff 46 0))]; rm_tcell] None (rm_sfacts [(21%nat, mkAF IMG_LO IMG_TOP 0)]).
(* the shadow the token engine reads for the table cell *)
Definition RM_SHT : list shent := [mkSHE 21 0 8].
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator laws at the harness head length cf_head (the A' instance's laws PALibA.palib_laws_A are at cf_head):
   field 14 (alx_hshadow) is a harness block's user-bytes shadow, field 22 (alx_hhead) its head poison *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib (PI := PA) B.
(* the callee texts, K0's kit of record origin/cold/h-hpreset-7-walkkit-next decff67d721f (PRH_FnPj.v a21e5a5cb897) *)
Hypothesis PJ_GET : PRH_FnPj.tpj_get_specX (PI := prh_img_A) (PA := PA) B ARx SK.
Hypothesis PJ_GET_STR : PRH_FnPj.tpj_get_str_specX (PI := prh_img_A) (PA := PA) B ARx SK.
Hypothesis RM_IMG : (forall k n, In (k, n) (rm_keys (PA := PA)) -> kept_img (PA := PA) B k (n + 1) /\
     (forall a, k / 64 * 64 <= a < (k + n) / 64 * 64 + 64 ->
        in_zs B (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const B ly))) /\
   kept_img (PA := PA) B (VAL (A_OBJ 3)) 48 /\
   Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).

#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
(* ---- image facts of PA, discharged at PI_prog_A by computation (rm_img_A at the end) ---- *)
(* the image's own byte at a (the value arodata_okP compares the view with) *)
Definition rm_rom (a : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a)).
(* the entry, the shadow-base GOT word and cell, the image start *)
Hypothesis Hent : SIGMA AS_read_members = BASE + AF_rm.
Hypothesis Hobj_lo : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd.
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
Hypothesis PAH : @pa_hi _ _ PA = IMG_TOP.
(* the thirteen key literals: n non-NUL bytes, then the NUL, the rest of the granules image bytes *)
Hypothesis Hlits : forall k n, In (k, n) (rm_keys (PA := PA)) ->
  (forall j, 0 <= j < n -> exists c, rm_rom (k + j) = Some c /\ c <> 0) /\ rm_rom (k + n) = Some 0 /\
  (forall j, 0 <= j < n + 8 -> rm_rom (k + j) <> None).
(* the static table `top`: its i-th word is the i-th key's address *)
Hypothesis Htop_ptr : forall i, (i < 6)%nat ->
  rdword rm_rom (VAL (A_OBJ 3) + 8 * Z.of_nat i) = Some (fst (nth i (rm_keys (PA := PA)) (0, 0))).
(* no program static is a read-only byte *)
Hypothesis Hpst_ro : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> ~ Exists (in_zr a) PST.
(* the harness hides at least one word at a block's start (the texts' name; preset_head_wide at CfParams_preset) *)
Hypothesis HW : @prh_head_wide cp.

(* the entry env: the registers, the shadow base (atom 32), then the walk's extras *)
Definition rm_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)).

Lemma rm_stk : STK_pj_get (PI := prh_img_A) + 128 <= STK_read_members (PI := prh_img_A) /\
  STK_pj_get_str (PI := prh_img_A) + 128 <= STK_read_members (PI := prh_img_A) /\
  128 <= STK_read_members (PI := prh_img_A) /\ ESTACK = 4096 /\
  0 <= STK_pj_get (PI := prh_img_A) /\ 0 <= STK_pj_get_str (PI := prh_img_A).
Proof.
repeat split; first [apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma rm_entry : forall ly S Hp W (regs : bvmap 5 word) mem md ch xs,
  afn_pre_x SEGS B ARx (STK_read_members (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (rm_E regs xs) ss_rm (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rm)) mem (seg_rom SEGS))) /\
  sh_ok SEGS RM_Bx [] (rm_E regs xs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch xs HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ exact Hobj_lo. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
set (E := rm_E regs xs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold rm_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold rm_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold rm_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (PAImg := PA) (A_OBJ 0)) as R0.
pose proof (pa_val_range (PAImg := PA) (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_rm. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rm_regions, stack_region, got_regionP, bcell_regionP.
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
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RM_Bx SHADOW_OFF);
    [cbn [sv_denot RM_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold rm_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS1 FS2 FS3 Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rm_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS1 FS2 FS3 Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

#[local] Notation STKrm := (STK_read_members (PI := prh_img_A)).

(* ---- what the journal from read_members' entry keeps ---- *)
(* clause 9: every byte above the ceiling outside the own stack window *)
Lemma rm_keep_hi : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 a,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STKrm <= a < sp0) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 a HJ Ha Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G & _). exact (G a Ha Hw).
Qed.
(* clause 10: every byte of a live allocator block the journal keeps (FP is empty here) *)
Lemma rm_keep_blk : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 p n i,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
  aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 p n i HJ H1 H2 Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). apply (G p n i H1 H2 Hi).
intros (r & Hr & _). destruct Hr.
Qed.
(* clause 11: every read-only image byte that is neither a program static nor errno nor runtime-owned *)
Lemma rm_keep_img : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 a,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 a HJ Hi Ho He Hp0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). apply (G a Hi Ho He Hp0).
apply fp_spares_closed. unfold YI16.sink_open_fp. intros (r & Hr & _). destruct Hr.
Qed.
(* clause 12: every byte of a fake frame of the entry state, and its shadow *)
Lemma rm_keep_frm : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 cid pos a,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 cid pos a HJ Hin Hr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). apply (G cid pos a Hin Hr).
intros (r & Hx & _). destruct Hx.
Qed.
(* the layout the journal ends at has the same stack and top *)
Lemma rm_ly : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  ly_top ly' = ly_top ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 HJ.
pose proof HJ as (_ & G & _).
destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & Gt & Glo & Ghi & _). auto.
Qed.
(* the caller's frame chain, at the callee's stack pointer and the journal's end state *)
Lemma rm_achain : forall ly S Hp W regs mem md ly' S' Hp' W' mem' md' k sp' v ch0,
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  astk_ok STKrm ly (spZ regs) ->
  achain ly (aview SEGS (w_H W) mem) (spZ regs) v ch0 ->
  sp' <= spZ regs -> achain ly' (aview SEGS (w_H W') mem') sp' v ch0.
Proof.
intros ly S Hp W regs mem md ly' S' Hp' W' mem' md' k sp' v ch0 HJ Hstk Hc Hsp.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct (rm_ly ly S Hp W mem md ly' S' Hp' W' mem' md' k (spZ regs) HJ) as (Gt & _ & _).
apply (achain_lower ly' (aview SEGS (w_H W') mem') (spZ regs) sp' v ch0); [|exact Hsp].
apply (achain_ly_top ly ly' (aview SEGS (w_H W') mem') (spZ regs) v ch0 Gt).
apply (achain_kept ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') (spZ regs) v ch0 (spZ regs) Hc
  ltac:(lia) ltac:(lia)).
intros a Ha. apply (rm_keep_hi ly S Hp W mem md ly' S' Hp' W' mem' md' k (spZ regs) a HJ); lia.
Qed.

(* the read-only view at any state the journal from entry reaches (its image clause; no static is read-only) *)
Lemma rm_rod : forall ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0,
  AJ STKrm sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W') mem').
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 HJ HR a Hro Ho He.
rewrite (rm_keep_img ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 a HJ (gs_ro_img a Hro) Ho He (Hpst_ro a Hro)).
exact (HR a Hro Ho He).
Qed.

(* ---- the key literals and the table top, at any state ARx describes with the read-only view (RM_IMG, Hlits) ---- *)
Lemma rm_key : forall lyc Sc Hpc Wc memc mdc k n,
  ARx lyc Sc Hpc Wc memc mdc ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H Wc) memc) ->
  In (k, n) (rm_keys (PA := PA)) ->
  exists l, Z.of_nat (length l) = n /\ cstr_ok (PA := PA) Wc memc k l.
Proof.
intros lyc Sc Hpc Wc memc mdc k n HAR HROD Hin.
pose proof RM_IMG as (RI & _ & ZAL).
destruct (RI k n Hin) as ((KLO & KHI & KB) & KSH).
destruct (Hlits k n Hin) as (L1 & L2 & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hn : 0 <= n).
{ clear - Hin. unfold rm_keys in Hin. apply in_map_iff in Hin as ([o m] & E & Hin). cbn [fst snd] in E.
  injection E as _ Em. rewrite <- Em. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as _ Hm; rewrite <- Hm; lia |]). destruct Hin. }
(* the shadow byte of a byte with ro_shadow_ok, from the zero-shadow ranges or the const shadow cells *)
assert (SH : forall a, ro_shadow_ok B a ->
  exists s, aview SEGS (w_H Wc) memc (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s).
{ intros a [(q & m & Hqm & Hq & Hm) | (v & Hv & Hvr)].
  - exists 0. split; [|left; reflexivity].
    pose proof (alx_zshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR (in_cons _ _ _ Hqm)) as Z0.
    pose proof (proj1 (Forall_forall _ _) ZAL (q, m) Hqm) as [Aq Am]. cbn [fst snd] in Z0, Aq, Am.
    specialize (Z0 (a / 8 - q / 8)). unfold shadow_of_addr in Z0 |- *.
    replace (SHADOW_OFF + a / 8) with (SHADOW_OFF + q / 8 + (a / 8 - q / 8)) by ring.
    apply Z0. clear - Hq Hm Aq Am. lia.
  - exists v. split; [|destruct Hvr as [-> | Hvr]; [left; reflexivity | right; exact Hvr]].
    pose proof (alx_const_cells _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as CC.
    pose proof (proj1 (Forall_forall _ _) CC _ (Hv lyc)) as Hc.
    cbn [cell_holds z1 c1 c_at c_val c_w aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). cbn [Z.of_nat] in Hc. rewrite Z.add_0_r in Hc.
    change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite Hc. f_equal.
    assert (Hv8 : 0 <= v < 256) by (clear - Hvr; lia).
    unfold YG0f.le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
    rewrite !(Z.mod_small v 256) by exact Hv8. reflexivity. }
(* presence of a shadow byte: a zero-shadow granule or a const shadow cell of any value *)
assert (SP : forall a, (in_zs B (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const B ly)) ->
  exists s, aview SEGS (w_H Wc) memc (shadow_of_addr SHADOW_OFF a) = Some s).
{ intros a [Hz | (v & Hv)].
  - destruct (SH a (or_introl Hz)) as (s & Hs & _). exists s. exact Hs.
  - pose proof (alx_const_cells _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as CC.
    pose proof (proj1 (Forall_forall _ _) CC _ (Hv lyc)) as Hc.
    cbn [cell_holds z1 c1 c_at c_val c_w aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). cbn [Z.of_nat] in Hc. rewrite Z.add_0_r in Hc.
    change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite Hc. eexists. reflexivity. }
assert (HR : forall j, 0 <= j <= n -> aview SEGS (w_H Wc) memc (k + j) = rm_rom (k + j)).
{ intros j Hj. destruct (KB (k + j) ltac:(clear - Hj; lia)) as (R1 & R2 & R3 & _). exact (HROD (k + j) R1 R2 R3). }
pose (f := fun j : nat => match rm_rom (k + Z.of_nat j) with Some c => c | None => 0 end).
pose (l := map f (seq 0 (Z.to_nat n))).
assert (Hll : length l = Z.to_nat n) by (unfold l; rewrite length_map, length_seq; reflexivity).
assert (Hlen : Z.of_nat (length l) = n) by (rewrite Hll; apply Z2Nat.id; exact Hn).
assert (Hnth : forall j, (j < Z.to_nat n)%nat -> nth j l 0 = f j).
{ intros j Hj. unfold l. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity. }
assert (HF : Forall (fun c => c <> 0) l).
{ apply Forall_forall. intros x Hx. unfold l in Hx. apply in_map_iff in Hx as (j & <- & Hj). apply in_seq in Hj.
  destruct (L1 (Z.of_nat j) ltac:(clear - Hj Hn; lia)) as (c & Hc & Hc0). cbv beta delta [f]. rewrite Hc. exact Hc0. }
assert (HG : garr8 SEGS (mrestrict (w_H Wc) memc) k (l ++ [0])).
{ intros j Hj. rewrite length_app, Hll in Hj. cbn [length] in Hj.
  assert (Ev : exists c, aview SEGS (w_H Wc) memc (k + Z.of_nat j) = Some c /\ nth j (l ++ [0]) 0 = c).
  { destruct (Nat.lt_ge_cases j (Z.to_nat n)) as [Hjl | Hjl].
    - destruct (L1 (Z.of_nat j) ltac:(clear - Hjl Hn; lia)) as (c & Hc & _). exists c. split.
      + rewrite HR by (clear - Hjl Hn; lia). exact Hc.
      + rewrite app_nth1 by (rewrite Hll; exact Hjl). rewrite (Hnth j Hjl). cbv beta delta [f]. rewrite Hc. reflexivity.
    - assert (Ej : j = Z.to_nat n) by (clear - Hj Hjl; lia). subst j. exists 0. split.
      + rewrite Z2Nat.id by exact Hn. rewrite HR by (clear - Hn; lia). exact L2.
      + rewrite app_nth2 by (rewrite Hll; lia). rewrite Hll, Nat.sub_diag. reflexivity. }
  destruct Ev as (c & Hc & ->).
  unfold aview in Hc. destruct (mbyte SEGS (mrestrict (w_H Wc) memc) (k + Z.of_nat j)) as [b|] eqn:Eb;
    cbn [option_map] in Hc; [|discriminate Hc].
  injection Hc as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|exact Hr]. intros kk Hk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
  unfold YO0f.le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite !(Z.mod_small (bv_unsigned b) 256) by exact Hr.
  symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
exists l. split; [exact Hlen|].
unfold cstr_ok, cstr. rewrite Hlen.
rewrite PAB in KLO. rewrite PAH in KHI. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in KLO, KHI.
split; [split; [exact HG | exact HF]|].
split; [clear - KLO; lia|].
split; [clear - KHI C1; lia|].
split; [clear - KLO KHI; lia|].
split; [unfold YGcfStr.amem_range8; left; rewrite C5; clear - KLO KHI; lia|].
split.
{ intros x Hx. apply SH. destruct (KB x Hx) as (_ & _ & _ & R4). exact R4. }
split.
{ intros s Hs. unfold shadow_addr in Hs.
  assert (E1 : (SHADOW_OFF + k / 8) / 8 * 8 = SHADOW_OFF + k / 64 * 8) by (unfold SHADOW_OFF; clear; lia).
  assert (E2 : (SHADOW_OFF + (k + (n + 1) - 1) / 8) / 8 * 8 = SHADOW_OFF + (k + n) / 64 * 8)
    by (unfold SHADOW_OFF; clear; lia).
  rewrite E1, E2 in Hs.
  destruct (SP (8 * (s - SHADOW_OFF)) (KSH (8 * (s - SHADOW_OFF)) ltac:(clear - Hs; lia))) as (sv & Hsv).
  unfold shadow_of_addr in Hsv.
  replace (SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8) with s in Hsv by (clear; lia).
  rewrite Hsv. discriminate. }
intros a Ha.
pose proof (L3 (a - k) ltac:(clear - Ha Hn; lia)) as Hro. replace (k + (a - k)) with a in Hro by ring.
unfold rm_rom in Hro. unfold aview, mbyte.
destruct (mrestrict (w_H Wc) memc (Z_to_bv 64 a)) as [b|]; [cbn [option_map]; discriminate | exact Hro].
Qed.
Lemma rm_top : forall lyc Sc Hpc Wc memc mdc i,
  ARx lyc Sc Hpc Wc memc mdc ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H Wc) memc) ->
  (i < 6)%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_OBJ 3) + 8 * Z.of_nat i) 8 (fst (nth i (rm_keys (PA := PA)) (0, 0))) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (VAL (A_OBJ 3) + 8 * Z.of_nat i) 8.
Proof.
intros lyc Sc Hpc Wc memc mdc i HAR HROD Hi.
pose proof RM_IMG as (_ & (TLO & THI & TB) & ZAL).
(* the shadow byte of a byte with ro_shadow_ok, from the zero-shadow ranges or the const shadow cells *)
assert (SH : forall a, ro_shadow_ok B a ->
  exists s, aview SEGS (w_H Wc) memc (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s).
{ intros a [(q & m & Hqm & Hq & Hm) | (v & Hv & Hvr)].
  - exists 0. split; [|left; reflexivity].
    pose proof (alx_zshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR (in_cons _ _ _ Hqm)) as Z0.
    pose proof (proj1 (Forall_forall _ _) ZAL (q, m) Hqm) as [Aq Am]. cbn [fst snd] in Z0, Aq, Am.
    specialize (Z0 (a / 8 - q / 8)). unfold shadow_of_addr in Z0 |- *.
    replace (SHADOW_OFF + a / 8) with (SHADOW_OFF + q / 8 + (a / 8 - q / 8)) by ring.
    apply Z0. clear - Hq Hm Aq Am. lia.
  - exists v. split; [|destruct Hvr as [-> | Hvr]; [left; reflexivity | right; exact Hvr]].
    pose proof (alx_const_cells _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as CC.
    pose proof (proj1 (Forall_forall _ _) CC _ (Hv lyc)) as Hc.
    cbn [cell_holds z1 c1 c_at c_val c_w aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). cbn [Z.of_nat] in Hc. rewrite Z.add_0_r in Hc.
    change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite Hc. f_equal.
    assert (Hv8 : 0 <= v < 256) by (clear - Hvr; lia).
    unfold YG0f.le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
    rewrite !(Z.mod_small v 256) by exact Hv8. reflexivity. }
assert (HR : forall j, 0 <= j < 8 ->
  aview SEGS (w_H Wc) memc (VAL (A_OBJ 3) + 8 * Z.of_nat i + j) = rm_rom (VAL (A_OBJ 3) + 8 * Z.of_nat i + j)).
{ intros j Hj. destruct (TB (VAL (A_OBJ 3) + 8 * Z.of_nat i + j) ltac:(clear - Hi Hj; lia)) as (R1 & R2 & R3 & _).
  exact (HROD _ R1 R2 R3). }
split.
- apply (val_mem_of_rdword SEGS (w_H Wc) memc). rewrite <- (Htop_ptr i Hi). unfold rdword.
  pose proof (HR 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  rewrite E0, (HR 1), (HR 2), (HR 3), (HR 4), (HR 5), (HR 6), (HR 7) by lia. reflexivity.
- intros x Hx. apply SH. destruct (TB x ltac:(clear - Hi Hx; lia)) as (_ & _ & _ & R4). exact R4.
Qed.

(* ---- the document's root at a callee of read_members, after any of read_members' earlier calls ---- *)
Lemma rm_root : forall ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own lyc Wc memc mdc kc (rc : bvmap 5 word) STK1,
  afn_pre_x SEGS B ARx STKrm ly S Hp W regs mem md ch ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) doc t D ->
  prhPj_rslot (PA := PA) B STKrm ly S W regs mem doc ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc ->
  ablocks B lyc S = ablocks B ly S ->
  spZ rc = spZ regs - 128 -> 0 <= STK1 -> STK1 + 128 <= STKrm ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam) doc t D /\
  prhPj_rslot (PA := PA) B STK1 lyc S Wc rc memc doc.
Proof.
intros ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own lyc Wc memc mdc kc rgc STK1
  HPRE Hnode Hrs HLED HJ Hbl Hsp HS0 HS1.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (HARc & Hle & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof cf_head_nonneg as C0. pose proof cf_head_al as C8.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
destruct (rm_ly ly S Hp W mem md lyc S Hp Wc memc mdc kc (spZ regs) HJ) as (Gt & Glo & Ghi).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc HAR Hle) as (_ & Hfa & _).
unfold prhPj_rslot in Hrs. destruct Hrs as (H4096 & Hpl & Hamr & Hex & Hra & Hhv).
(* the bytes of a live block, a fake frame of the entry state, and the real stack above the entry sp are kept *)
assert (HBK : forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n ->
  mrestrict (w_H Wc) memc (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros b n x Hb Hx.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (_ & B4096 & Bcl & _).
  assert (Hb' : In (b, n) (ablocks B lyc S)) by (rewrite Hbl; exact Hb).
  pose proof (rm_keep_blk ly S Hp W mem md lyc S Hp Wc memc mdc kc (spZ regs) b n (x - b) HJ Hb Hb'
    ltac:(clear - Hx; lia)) as E.
  replace (b + (x - b)) with x in E by ring.
  apply (gs_raw_of_aview (PA := PA) (w_H W) (w_H Wc) mem memc x); [clear - Hx B4096 Bcl C1; lia | | exact E].
  refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)).
  left. exists b, n. split; [exact Hb | exact Hx]. }
assert (HFK : forall cid pos x, In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  mrestrict (w_H Wc) memc (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros cid pos x Hf Hx.
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos HAR Hf) as (F4096 & Fcl & _).
  pose proof (rm_keep_frm ly S Hp W mem md lyc S Hp Wc memc mdc kc (spZ regs) cid pos x HJ Hf
    ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; exact Hx)) as E.
  apply (gs_raw_of_aview (PA := PA) (w_H W) (w_H Wc) mem memc x); [clear - Hx F4096 Fcl C1; lia | | exact E].
  refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)).
  right. left. exists cid, pos. split; [exact Hf | exact Hx]. }
assert (HSK : forall x, spZ regs <= x < ly_top ly ->
  mrestrict (w_H Wc) memc (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros x Hx.
  pose proof (rm_keep_hi ly S Hp W mem md lyc S Hp Wc memc mdc kc (spZ regs) x HJ
    ltac:(clear - Hx Hceil Hslo Hstk0 Htop2 H47; lia) ltac:(clear - Hx; lia)) as E.
  apply (gs_raw_of_aview (PA := PA) (w_H W) (w_H Wc) mem memc x);
    [clear - Hx Hceil Hslo Hstk0 Htop2 H47 C1; lia | | exact E].
  intros Hi. pose proof (Hsegs x Hi) as Hl. clear - Hl Hx Hceil Hslo Hstk0 C1 C5. lia. }
(* every ledger block's byte is kept (rm_lam_kept's argument) *)
assert (HLK : forall a k x, In (a, k) Lam -> a <= x < a + k ->
  mrestrict (w_H Wc) memc (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros a k x Hin Hx.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as Hb.
  unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & _).
  assert (Hrq : req_size (k + cf_head) = k + cf_head) by (apply gs_req; clear - Hx C0; lia).
  apply (HBK (a - cf_head) (k + cf_head) x Hab). rewrite Hrq. clear - Hx C0. lia. }
(* a visible hull covers a sub-range's hull *)
assert (HSUB : forall (rd : reader) p m, shadow_hull_vis rd p m -> p <= doc -> doc + 56 <= p + m ->
  shadow_hull_vis rd doc 56).
{ intros rd p m Hh Hq1 Hq2 s Hs. apply Hh.
  assert (M : forall u v, u <= v -> shadow_addr u / 8 * 8 <= shadow_addr v / 8 * 8).
  { intros u v Huv. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [clear; lia|].
    apply Z.div_le_mono; [clear; lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; [clear; lia | exact Huv]. }
  pose proof (M p doc Hq1) as M1. pose proof (M (doc + 56 - 1) (p + m - 1) ltac:(clear - Hq2; lia)) as M2.
  clear - Hs M1 M2. lia. }
split.
(* (a) the tree: its footprint's bytes are kept *)
{ apply (pj_nodeR_frame SEGS t _ _ (prh_lin Lam) doc D Hnode).
  apply (gs_agree (PA := PA)). intros x [Hx | (b & Hb & Hx)].
  - destruct Hpl as [(b & n & Hb & Hb1 & Hb2) | [(cid & pos & Hf & Hf1 & Hf2) | (Hs1 & Hs2)]].
    + apply (HBK b n x Hb). clear - Hx Hb1 Hb2. lia.
    + apply (HFK cid pos x Hf). clear - Hx Hf1 Hf2. lia.
    + apply HSK. clear - Hx Hs1 Hs2. lia.
  - pose proof (pj_nodeR_lblk (PA := PA) t _ (prh_lin Lam) doc D Hnode b Hb) as Hl. unfold prh_lin in Hl.
    destruct b as [a k]. unfold pj_holdsR in Hx. cbn [fst snd] in Hl, Hx.
    exact (HLK a k x Hl Hx). }
(* (b) the root slot at the callee *)
unfold prhPj_rslot.
split; [exact H4096|].
split.
{ destruct Hpl as [(b & n & Hb & Hb1 & Hb2) | [(cid & pos & Hf & Hf1 & Hf2) | (Hs1 & Hs2)]].
  - left. exists b, n. rewrite Hbl. split; [exact Hb | split; [exact Hb1 | exact Hb2]].
  - right; left. exists cid, pos. rewrite !Hfa. split; [exact Hf | split; [exact Hf1 | exact Hf2]].
  - right; right. rewrite Gt. clear - Hs1 Hs2 Hsp. lia. }
split; [exact Hamr|].
split.
{ intros a Ha Hw. apply (Hex a Ha). clear - Hw Hsp HS1. lia. }
destruct Hpl as [(b & n & Hb & Hb1 & Hb2) | [(cid & pos & Hf & Hf1 & Hf2) | (Hs1 & Hs2)]].
- (* a live allocator block *)
  assert (Hbc : In (b, n) (ablocks B lyc S)) by (rewrite Hbl; exact Hb).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (B16 & B4096 & Bcl & _).
  destruct (in_dec Z.eq_dec b Hp) as [Hh | Hh].
  + (* a harness block: the root is past the hidden head *)
    destruct (alx_hshadow _ _ _ LAWS lyc S Hp Wc memc mdc b n HARc Hbc Hh) as [Hbs Hhu].
    assert (Hd : b + cf_head <= doc).
    { destruct (Z_le_gt_dec (b + cf_head) doc) as [Q | Q]; [exact Q | exfalso].
      assert (Hh0 : b <= doc < b + cf_head) by (clear - Q Hb1; lia).
      exact (hhead_not_addressable_x _ _ _ LAWS ly S Hp W mem md b n doc 56 HAR Hb Hh Hh0 ltac:(clear; lia) Hra). }
    split.
    * eapply block_shadow_range; [exact Hbs | clear - Hd; lia | clear - Hb2; lia].
    * apply (HSUB _ (b + cf_head) (req_size n - cf_head)); [| clear - Hd; lia | clear - Hb2; lia].
      apply Hhu. clear - Hd Hb2. lia.
  + (* not a harness block: no hidden head lies in it *)
    assert (Hnh : forall h, In h Hp -> ~ (b <= h < b + req_size n)).
    { intros h Hin Hr. pose proof HLED as (_ & _ & _ & HP).
      apply (Permutation_in _ HP) in Hin. apply in_map_iff in Hin as ([a k] & Eh & Hin). cbn [fst] in Eh. subst h.
      pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as Hhb.
      unfold prh_hblock in Hhb. destruct Hhb as (Hk0 & Hab & Hhp & _).
      assert (Hne : (a - cf_head, k + cf_head) <> (b, n)).
      { intros Eq. injection Eq as E1 _. apply Hh. rewrite <- E1. exact Hhp. }
      pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hb Hne) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
      assert (Hk1 : 0 <= k + cf_head) by (clear - Hk0 C0; lia).
      pose proof (prh_req_size_pos (k + cf_head) Hk1) as Hpos.
      clear - Hdj Hr Hpos. lia. }
    destruct (alx_shadow _ _ _ LAWS lyc S Hp Wc memc mdc b n HARc Hbc Hnh) as [Hbs Hhu].
    split.
    * eapply block_shadow_range; [exact Hbs | exact Hb1 | exact Hb2].
    * exact (HSUB _ b (req_size n) Hhu Hb1 Hb2).
- (* a fake frame of the entry state: the journal keeps its shadow *)
  pose proof (lo_F_al _ (alx_layout_ok _ _ _ LAWS ly S Hp W mem md HAR)) as LF. unfold page_aligned in LF.
  assert (Hc0 : 0 <= cid).
  { destruct (Z_le_gt_dec 0 cid) as [Q | Q]; [exact Q | exfalso].
    assert (Hfb : fs_frame_bytes cid <= 32).
    { unfold fs_frame_bytes. rewrite <- (Z.opp_involutive cid), Z.shiftl_opp_r.
      rewrite Z.shiftr_div_pow2 by (clear - Q; lia).
      assert (P2 : 2 <= 2 ^ (- cid)).
      { change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; [clear; lia | clear - Q; lia]. }
      apply Z.div_le_upper_bound; [clear - P2; lia|]. clear - P2. lia. }
    clear - Hfb Hf1 Hf2. lia. }
  pose proof (fs_frame_bytes_eq cid Hc0) as Efb.
  assert (Fm : frame_addr ly cid pos mod 64 = 0).
  { unfold frame_addr, fs_frame_off, kFakeFramesOff, kStackSizeLog. rewrite Efb.
    change (Z.shiftl 1 20) with 1048576.
    replace (pos * (64 * 2 ^ cid)) with (64 * (pos * 2 ^ cid)) by ring.
    generalize (pos * 2 ^ cid). intros q. clear - LF. lia. }
  assert (Fb : fs_frame_bytes cid mod 64 = 0).
  { rewrite Efb. generalize (2 ^ cid). intros r. clear. lia. }
  assert (HFS : forall y, shadow_addr (frame_addr ly cid pos) <= y <
      shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
    aview SEGS (w_H Wc) memc y = aview SEGS (w_H W) mem y).
  { intros y Hy. apply (rm_keep_frm ly S Hp W mem md lyc S Hp Wc memc mdc kc (spZ regs) cid pos y HJ Hf).
    right. unfold in_zr. cbn [fst snd]. exact Hy. }
  clear - HFS Hra Hhv Hf1 Hf2 Fm Fb.
  set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *. clearbody fa fb.
  split.
  + intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. apply HFS. unfold shadow_of_addr, shadow_addr. clear - Hx Hf1 Hf2 Fm Fb. lia.
  + intros s Hs. rewrite (HFS s); [exact (Hhv s Hs)|].
    unfold shadow_addr in *. clear - Hs Hf1 Hf2 Fm Fb. unfold SHADOW_OFF in *. lia.
- (* the real stack at or above the entry sp: its shadow reads 0 *)
  destruct (stk_aligned_x _ _ _ LAWS lyc S Hp Wc memc mdc HARc) as (SA1 & SA2).
  rewrite Glo in SA1. rewrite Ghi in SA2.
  assert (HZ : forall y, ly_stk_lo ly <= y < ly_stk_hi ly ->
    aview SEGS (w_H Wc) memc (SHADOW_OFF + y / 8) = Some 0).
  { intros y Hy. apply (alx_zshadow_byte _ _ _ LAWS lyc S Hp Wc memc mdc y HARc). rewrite Glo, Ghi. exact Hy. }
  split.
  + intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply HZ.
    clear - Hx Hs1 Hs2 Hslo Hstk0 Htop2. lia.
  + intros s Hs.
    assert (Es : s = SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8) by (clear; lia).
    rewrite Es, (HZ (8 * (s - SHADOW_OFF))); [discriminate|].
    unfold shadow_addr in Hs. clear - Hs Hs1 Hs2 SA1 SA2 Hslo Hstk0 Htop2. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- a node below the root: a 56-byte cell of a ledger block's user range (LAWS' field 14, alx_hshadow) ---- *)
Lemma rm_sub_rslot : forall ly S Hp W mem Lam peak cnt fail ran most own lyc Wc memc mdc (rc : bvmap 5 word) STK1 kids cap i,
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx lyc S Hp Wc memc mdc -> ablocks B lyc S = ablocks B ly S ->
  In (kids, 56 * cap) Lam -> 0 <= i < cap ->
  YM05.alloc_ceiling <= spZ rc - STK1 ->
  prhPj_rslot (PA := PA) B STK1 lyc S Wc rc memc (kids + 56 * i).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own lyc Wc memc mdc rgs STK1 kids cap i HLd HAR Hbl Hin Hi Hceil.
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran kids (56 * cap) most own HLd Hin) as Hb.
unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & Hhp & _).
rewrite <- Hbl in Hab.
pose proof cf_head_nonneg as C0.
destruct (alx_blocks _ _ _ LAWS lyc S Hp Wc memc mdc _ _ HAR Hab) as (_ & H4096 & Hcl & Happ & _).
assert (Hrq : req_size (56 * cap + cf_head) = 56 * cap + cf_head) by (apply gs_req; clear - Hi C0; lia).
rewrite Hrq in Hcl, Happ.
destruct (alx_hshadow _ _ _ LAWS lyc S Hp Wc memc mdc _ _ HAR Hab Hhp) as [Hbs Hhu].
rewrite Hrq in Hbs, Hhu.
replace (kids - cf_head + cf_head) with kids in Hbs, Hhu by (clear; lia).
replace (56 * cap + cf_head - cf_head) with (56 * cap) in Hbs, Hhu by (clear; lia).
specialize (Hhu ltac:(clear - Hi C0; lia)).
pose proof ASAN_CEIL_range as [CR _].
unfold prhPj_rslot.
split; [clear - H4096 C0 Hi; lia|].
split; [left; exists (kids - cf_head), (56 * cap + cf_head); rewrite Hrq; split; [exact Hab | clear - Hi C0; lia]|].
split.
{ unfold amem_range. unfold in_app in Happ. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
  - left. unfold kLowShadowBeg, kLowMemEnd in *. clear - Hlow Hi C0; lia.
  - right. unfold kHighMemEnd in *. split; [clear - Hh1 Hi C0; lia | clear - Hh2 CR Hi C0; lia]. }
split.
{ intros a Ha. clear - Ha Hcl Hceil Hi. lia. }
split.
{ eapply block_shadow_range; [exact Hbs | clear - Hi; lia | clear - Hi; lia]. }
intros s Hs. apply Hhu.
assert (M : forall u v, u <= v -> shadow_addr u / 8 * 8 <= shadow_addr v / 8 * 8).
{ intros u v Huv. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [clear; lia|].
  apply Z.div_le_mono; [clear; lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; [clear; lia | exact Huv]. }
pose proof (M kids (kids + 56 * i) ltac:(clear - Hi; lia)) as M1.
pose proof (M (kids + 56 * i + 56 - 1) (kids + 56 * cap - 1) ltac:(clear - Hi; lia)) as M2.
clear - Hs M1 M2. lia.
Qed.
(* every byte of a ledger block agrees with the entry at any state the journal from entry reaches *)
Lemma rm_lam_kept : forall ly S Hp W mem md Lam peak cnt fail ran most own lyc Wc memc mdc kc sp0,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ STKrm sp0 [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc ->
  ablocks B lyc S = ablocks B ly S ->
  forall a k x, In (a, k) Lam -> a <= x < a + k ->
    mrestrict (w_H Wc) memc (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own lyc Wc memc mdc kc sp0 HAR HLd HJ Hbl a k x Hin Hx.
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLd Hin) as Hb.
unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & _).
pose proof cf_head_nonneg as C0.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (apply gs_req; clear - Hx C0; lia).
rewrite Hrq in Hcl.
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
assert (Hab' : In (a - cf_head, k + cf_head) (ablocks B lyc S)) by (rewrite Hbl; exact Hab).
pose proof (rm_keep_blk ly S Hp W mem md lyc S Hp Wc memc mdc kc sp0 (a - cf_head) (k + cf_head) (x - (a - cf_head))
  HJ Hab Hab' ltac:(rewrite Hrq; clear - Hx C0; lia)) as E.
replace (a - cf_head + (x - (a - cf_head))) with x in E by (clear; lia).
assert (Hni : ~ in_img SEGS x).
{ refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md x HAR _)).
  left. exists (a - cf_head), (k + cf_head). split; [exact Hab | rewrite Hrq; clear - Hx C0; lia]. }
apply (gs_raw_of_aview (PA := PA) (w_H W) (w_H Wc) mem memc x); [clear - Hx H4096 Hcl CR C0; lia | exact Hni | exact E].
Qed.
(* a node over the ledger's blocks is the same node at any memory that keeps its footprint's bytes *)
Lemma rm_node_move : forall (Wx Wy : world SEGS) memx memy Lam z v Dz,
  pj_nodeR SEGS (mrestrict (w_H Wx) memx) (prh_lin Lam) z v Dz ->
  (forall x, pj_footR z Dz x -> mrestrict (w_H Wy) memy (Z_to_bv 64 x) = mrestrict (w_H Wx) memx (Z_to_bv 64 x)) ->
  pj_nodeR SEGS (mrestrict (w_H Wy) memy) (prh_lin Lam) z v Dz.
Proof.
intros Wx Wy memx memy Lam z v Dz Hn Hk.
apply (pj_nodeR_frame SEGS v _ _ (prh_lin Lam) z Dz Hn).
apply (gs_agree (PA := PA)). intros x Hx. exact (Hk x Hx).
Qed.
(* the footprint of a node in a ledger block's cell lies in ledger blocks *)
Lemma rm_foot_lam : forall m Lam z v Dz kids cap i,
  pj_nodeR SEGS m (prh_lin Lam) z v Dz -> In (kids, 56 * cap) Lam -> z = kids + 56 * i -> 0 <= i < cap ->
  forall x, pj_footR z Dz x -> exists a k, In (a, k) Lam /\ a <= x < a + k.
Proof.
intros m Lam z v Dz kids cap i Hn Hk Ez Hi x [Hx | (b & Hb & Hx)].
- exists kids, (56 * cap). split; [exact Hk | lia].
- pose proof (pj_nodeR_lblk (PA := PA) v m (prh_lin Lam) z Dz Hn b Hb) as Hl. unfold prh_lin in Hl.
  destruct b as [a k]. exists a, k. split; [exact Hl|]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. exact Hx.
Qed.

(* a re-seat's env: the registers, the shadow base (atom 32), the thirteen saved registers' entry values (atoms 33 ..
   45, rm_saves' order), then the seat's extras (atoms 46 ..) *)
Definition rm_EL (regsL regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA
    (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) xs)).


(* a register at an exit, from the state HS: a saved register from the frame (EX), sp (U2, SpL), gp / tp (ER, R3, R4) *)
Ltac rm_back HS OLD EX ER U2 SpL R3 R4 :=
  lazymatch goal with |- getr _ ?r = _ =>
    let G := fresh "G" in
    pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
    lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end;
    rewrite G; clear G; cbn [sv_denot]; rewrite ?OLD by lia;
    first [ lazymatch goal with |- context [ew _ ?q] =>
              let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
            rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            reflexivity
          | rewrite U2, SpL, Z.sub_add; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lazymatch goal with |- context [ew _ ?q] => rewrite (ER q r) by (lia || reflexivity) end;
            rewrite Z.add_0_r, Z_to_bv_bv_unsigned; first [exact R3 | exact R4] ]
  end.

(* ======== the segments after the entry, each from a re-seat over the entry state ======== *)
Section ent.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : jv) (D Lam : list (Z * Z)) (peak cnt fail ran most own : Z).
Hypothesis HPRE : afn_pre_x SEGS B ARx STKrm ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem).
Hypothesis Hnode : pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) doc t D.
Hypothesis Hrs : prhPj_rslot (PA := PA) B STKrm ly S W regs mem doc.
Hypothesis HLED : prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.
(* FRM0-ENTRY (lib/A/PRH_Base.v fpre): fpre's last conjunct, the rounding mode at entry; the walk runs no float
   instruction, so the same fact is the callee's entry conjunct at every call *)
Hypothesis HFRM : YK0o.frm_zero (@YK11.fp_csr fx).

(* The post, named *)
Definition rm_Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger (PI := prh_img_A) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
  (room_live_cf S -> room_live_cf S') /\ pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) doc t D.
Definition rm_goal (WL : world SEGS) (c : config) : Prop :=
  SRr SEGS WL c (fpostm (PI := prh_img_A) (PA := PA) B ARx SK STKrm [] regs ly S Hp W mem md rm_Q).
(* what every seat carries: the journal from the entry, the memnorm keep, the blocks, the ledger, the saved registers
   in the frame, sp / gp / tp *)
Definition rm_base (lyL : alayout) (WL : world SEGS) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model)
  (kL : Z) : Prop :=
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyL S Hp WL memL mdL kL /\
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memL) /\
  ablocks B lyL S = ablocks B ly S /\
  prh_ledger (PI := prh_img_A) (PA := PA) B lyL S Hp WL memL Lam peak cnt fail ran most own /\
  Forall (fun sr => val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 128 + fst sr) 8 (bv_unsigned (getr regs (snd sr)))) rm_saves /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4.
(* a member pj_get returned (C1's params, C2's state): NULL, or a node in a cell of a ledger block, at the entry memory *)
Definition rm_res (z : Z) : Prop :=
  z = 0 \/ exists v Dz kd cd (j : nat), pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) z v Dz /\ In (kd, 56 * cd) Lam /\
    z = kd + 56 * Z.of_nat j /\ Z.of_nat j < cd.


(* the callee-saved registers (YG0d.v acallee_saved), as register names *)
Definition rm_allB : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma rm_aregs : forall (regsF : bvmap 5 word),
  (forall r : bv 5, In r rm_allB -> getr regsF r = getr regs r) -> aregs_preserved regs regsF.
Proof.
intros regsF H r Hr. apply H. unfold rm_allB. apply in_map. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto .. |].
assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H0 as [-> | H0]; [cbn; tauto|]). subst r. cbn; tauto.
Qed.
(* a member is NULL or below alloc_ceiling *)
Lemma rm_res_low : forall z, rm_res z -> 0 <= z /\ z + 56 <= YM05.alloc_ceiling.
Proof.
intros z [-> | (v & Dz & kd & cd & j & Hn & Hk & Ez & Hj)]; [pose proof asan_consts as (C1 & _); lia|].
pose proof HPRE as (HAR & _).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran kd (56 * cd) most own HLED Hk) as Hb.
unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & _).
pose proof cf_head_nonneg as C0.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
rewrite gs_req in Hcl by lia. lia.
Qed.
(* a member at a callee of read_members: NULL, or its node (at the call's memory) in a callee's root slot *)
Lemma rm_res_at : forall z lyc Wc memc mdc kc (rc : bvmap 5 word) STK1,
  rm_res z -> AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc -> ablocks B lyc S = ablocks B ly S ->
  YM05.alloc_ceiling <= spZ rc - STK1 ->
  z = 0 \/ exists v Dz, pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam) z v Dz /\
    prhPj_rslot (PA := PA) B STK1 lyc S Wc rc memc z.
Proof.
intros z lyc Wc memc mdc kc rcl STK1 [-> | (v & Dz & kd & cd & j & Hn & Hk & Ez & Hj)] HJ Hbl Hc; [left; reflexivity|].
right. exists v, Dz. pose proof HPRE as (HAR & _). pose proof HJ as (HARc & _).
split.
- apply (rm_node_move W Wc mem memc Lam z v Dz Hn).
  intros x Hx. destruct (rm_foot_lam _ Lam z v Dz kd cd (Z.of_nat j) Hn Hk Ez ltac:(lia) x Hx) as (a & k & Hin & Hax).
  exact (rm_lam_kept ly S Hp W mem md Lam peak cnt fail ran most own lyc Wc memc mdc kc (spZ regs) HAR HLED HJ Hbl
    a k x Hin Hax).
- rewrite Ez. exact (rm_sub_rslot ly S Hp W mem Lam peak cnt fail ran most own lyc Wc memc mdc rcl STK1 kd cd (Z.of_nat j)
    HLED HARc Hbl Hk ltac:(lia) Hc).
Qed.
(* the ledger at a memory that agrees below alloc_ceiling *)
Lemma rm_ledger_keep : forall lyc Wc m m' mdc,
  ARx lyc S Hp Wc m mdc ->
  prh_ledger (PI := prh_img_A) (PA := PA) B lyc S Hp Wc m Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  prh_ledger (PI := prh_img_A) (PA := PA) B lyc S Hp Wc m' Lam peak cnt fail ran most own.
Proof.
intros lyc Wc m m' mdc HARc HLg KL. pose proof asan_consts as (C1 & _).
apply (prh_ledger_kept_aview B lyc S Hp Wc m lyc S Hp Wc m' Lam peak cnt fail ran most own HLg).
- intros a Ha. apply KL. apply Exists_exists in Ha as (r & Hin & Hr). vm_compute in Hin. unfold in_zr in Hr.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
- intros a k0 i Hin Hi. pose proof HW as HWv. unfold prh_head_wide in HWv.
  destruct (prh_ledger_hblock B lyc S Hp Wc m Lam peak cnt fail ran a k0 most own HLg Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS lyc S Hp Wc m mdc (a - cf_head) (k0 + cf_head) HARc Hab) as (_ & H4096 & Hc & _).
  rewrite gs_req in Hc by lia. apply KL. clear -H4096 Hc Hi Hk0 HWv. lia.
- intros a k0 _ H. exact H.
- apply Permutation_refl.
Qed.
(* a frame-chain value below alloc_ceiling (s0 holds the state member from C2 on) *)
Lemma rm_achain_low : forall lyc rd sp v, v < YM05.alloc_ceiling -> achain lyc rd sp v [].
Proof. intros lyc rd sp v H. left. split; [left; exact H | reflexivity]. Qed.
(* every exit: the journal from the entry, the registers back, the post *)
Lemma rm_fin : forall lyF WF regsF memF mdF mat kF (rL : bvmap 5 word),
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyF S Hp WF memF mdF kF ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memF) ->
  ablocks B lyF S = ablocks B ly S ->
  prh_ledger (PI := prh_img_A) (PA := PA) B lyF S Hp WF memF Lam peak cnt fail ran most own ->
  (forall r : bv 5, In r rm_allB -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  spZ rL = spZ regs - 128 ->
  fpostm (PI := prh_img_A) (PA := PA) B ARx SK STKrm [] regs ly S Hp W mem md rm_Q WF
    (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros lyF WF regsF memF mdF mat kF rL HJ HPM Eab HLF Hkept G1 SpL.
pose proof HPRE as (HAR & Hra & _).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
unfold fpostm, fpost, apost_base_x.
exists lyF, S, Hp, regsF, memF, (with_vm_backing (m_vm_lazy mdF) mat mdF), kF.
split; [rewrite G1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact (rm_aregs regsF Hkept)|].
unfold fQmn, rm_Q. split; [|exact HPM].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Eab|]. split; [exact HLF|]. split; [intros H; exact H|].
exact (proj1 (rm_root ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own lyF WF memF mdF kF rL 0
  HPRE Hnode Hrs HLED HJ Eab SpL ltac:(lia) ltac:(lia))).
Qed.


(* ---- more support: cells of ledger blocks, their words at any later state, the frame's words from a seat's region ---- *)
Lemma rm_cell_low : forall kd cd (j : Z), In (kd, 56 * cd) Lam -> 0 <= j < cd ->
  4096 <= kd + 56 * j /\ kd + 56 * j + 56 <= YM05.alloc_ceiling.
Proof.
intros kd cd j Hk Hj. pose proof HPRE as (HAR & _).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran kd (56 * cd) most own HLED Hk) as Hb.
unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & _).
pose proof cf_head_nonneg as C0.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
rewrite gs_req in Hcl by lia. lia.
Qed.
Lemma rm_lam_view : forall lyc Wc memc mdc kc a k x,
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc -> ablocks B lyc S = ablocks B ly S ->
  In (a, k) Lam -> a <= x < a + k -> aview SEGS (w_H Wc) memc x = aview SEGS (w_H W) mem x.
Proof.
intros lyc Wc memc mdc kc a k x HJ Hbl Hin Hx. pose proof HPRE as (HAR & _).
unfold aview, mbyte.
rewrite (rm_lam_kept ly S Hp W mem md Lam peak cnt fail ran most own lyc Wc memc mdc kc (spZ regs) HAR HLED HJ Hbl a k x Hin Hx).
reflexivity.
Qed.
Lemma rm_val_lam : forall lyc Wc memc mdc kc kd cd a n v,
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc -> ablocks B lyc S = ablocks B ly S ->
  In (kd, 56 * cd) Lam -> kd <= a -> a + Z.of_nat n <= kd + 56 * cd ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H Wc) memc) a n v.
Proof.
intros lyc Wc memc mdc kc kd cd a n v HJ Hbl Hin H1 H2 Hv.
apply (val_mem_kept SEGS (w_H W) (w_H Wc) mem memc a n v); [|exact Hv].
intros q Hq. apply (rm_lam_view lyc Wc memc mdc kc kd (56 * cd) (a + q) HJ Hbl Hin). lia.
Qed.
Lemma rm_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D i u,
  pj_itemsR P a l D -> nth_error l i = Some u -> exists Di, P (a + 56 * Z.of_nat i) u Di.
Proof.
intros P l. induction l as [|u0 r IH]; intros a DD i u H Hi; [destruct i; discriminate Hi|].
cbn [pj_itemsR] in H. destruct H as (D1 & D2 & -> & H1 & H2).
destruct i as [|i]; cbn [nth_error] in Hi.
- injection Hi as <-. exists D1. rewrite Z.mul_0_r, Z.add_0_r. exact H1.
- destruct (IH (a + 56) D2 i u H2 Hi) as (Di & HDi). exists Di.
  replace (a + 56 * Z.of_nat (Datatypes.S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HDi.
Qed.
(* the shadow of a node in a ledger block's cell, as the token engine's shadow entry over its 56 bytes *)
Lemma rm_shok_node : forall (E' : env) lyc Wc memc mdc kc z1 kd cd j1,
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc -> ablocks B lyc S = ablocks B ly S ->
  In (kd, 56 * cd) Lam -> z1 = kd + 56 * Z.of_nat j1 -> Z.of_nat j1 < cd ->
  ew E' 32 = Z_to_bv 64 SHADOW_OFF -> ew E' 9 = Z_to_bv 64 z1 ->
  sh_ok SEGS RM_Bx RM_SHN E' (mrestrict (w_H Wc) memc).
Proof.
intros E' lyc Wc memc mdc kc z1 kd cd j1 HJ Hbl Hk Ez Hj E32 E9.
pose proof HJ as (HARc & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
destruct rm_stk as (_ & _ & FS3 & _).
pose proof (rm_cell_low kd cd (Z.of_nat j1) Hk ltac:(lia)) as (Z1 & Z2). rewrite <- Ez in Z1, Z2.
destruct (rm_sub_rslot ly S Hp W mem Lam peak cnt fail ran most own lyc Wc memc mdc regs STKrm kd cd (Z.of_nat j1)
  HLED HARc Hbl Hk ltac:(lia) ltac:(lia)) as (_ & _ & Hamr & _ & HRA & _).
rewrite <- Ez in Hamr, HRA.
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H Wc) memc E' RM_Bx 9 z1 56 z1 0 56 HRA).
- unfold RM_Bx. apply (U_atom E' 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
- apply (U_atom E' 9 z1 E9). lia.
- lia.
- lia.
- intros x Hx. unfold amem_range in Hamr. rewrite C3 in Hamr. rewrite C5 in Hamr. unfold SHADOW_OFF. lia.
Qed.
(* a node in a ledger block's cell is kept by a call whose journal keeps the live blocks *)
Lemma rm_node_kept : forall (E' : env) z1 kd cd j1 STK1 sp1 lyc Wc memc mdc ly2 W2 mem2 md2 k1 cs,
  AJ STK1 sp1 [] lyc S Hp Wc memc mdc [] ly2 S Hp W2 mem2 md2 k1 ->
  ARx lyc S Hp Wc memc mdc -> ablocks B lyc S = ablocks B ly S -> ablocks B ly2 S = ablocks B ly S ->
  In (kd, 56 * cd) Lam -> z1 = kd + 56 * Z.of_nat j1 -> Z.of_nat j1 < cd ->
  bv_unsigned (ew E' 9) = z1 ->
  region_kept SEGS E' (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 9%nat) 0 56 0 0 cs).
Proof.
intros E' z1 kd cd j1 STK1 sp1 lyc Wc memc mdc ly2 W2 mem2 md2 k1 cs HJ1 HARc Hb1 Hb2 Hk Ez Hj HU.
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran kd (56 * cd) most own HLED Hk) as Hb.
unfold prh_hblock in Hb. destruct Hb as (Hk0 & Hab & _).
pose proof cf_head_nonneg as C0. pose proof asan_consts as (C1 & _).
assert (Hab1 : In (kd - cf_head, 56 * cd + cf_head) (ablocks B lyc S)) by (rewrite Hb1; exact Hab).
assert (Hab2 : In (kd - cf_head, 56 * cd + cf_head) (ablocks B ly2 S)) by (rewrite Hb2; exact Hab).
destruct (alx_blocks _ _ _ LAWS lyc S Hp Wc memc mdc _ _ HARc Hab1) as (_ & H4096 & Hcl & _).
assert (Hrq : req_size (56 * cd + cf_head) = 56 * cd + cf_head) by (apply gs_req; lia).
rewrite Hrq in Hcl.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite HU; intros a Ha; [|lia].
pose proof (G (kd - cf_head) (56 * cd + cf_head) (a - (kd - cf_head)) Hab1 Hab2 ltac:(rewrite Hrq; lia)
  ltac:(intros (r & Hr & _); destruct Hr)) as E1.
replace (kd - cf_head + (a - (kd - cf_head))) with a in E1 by lia.
apply (mbyte_of_aview SEGS). exact E1.
Qed.
(* the frame's saved words and seen word from a seat's frame region (after any run or call that kept it) *)
Lemma rm_frame_facts : forall (E' : env) m xc e,
  region_ok SEGS E' m (rm_frame (xc ++ [YP09.mkChunk 16 (CVal 8 e)])) ->
  bv_unsigned (ew E' 2) = spZ regs - 128 ->
  (forall j0, (j0 < 13)%nat -> ew E' (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv)))) ->
  Forall (fun sr => val_mem SEGS m (spZ regs - 128 + fst sr) 8 (bv_unsigned (getr regs (snd sr)))) rm_saves /\
  val_mem SEGS m (spZ regs - 112) 8 (U E' e).
Proof.
intros E' m xc e HR HU HX. split.
- apply Forall_forall. intros sr Hsr. cbn [rm_saves In] in Hsr.
  repeat (destruct Hsr as [<- | Hsr];
    [ cbn [fst snd]; lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr regs ?r)) =>
        let j0 := eval vm_compute in (Z.to_nat ((120 - od) / 8)) in
        eapply (slot_of_region SEGS E' m _ _ _ _ _ _ _ (SOff (33 + j0) 0) _ HR HU);
        [ unfold rm_frame; apply in_or_app; right; cbn [app In]; repeat first [left; reflexivity | right]
        | rewrite (gs_denot_off E' (33 + j0) (bv_unsigned (getr regs r)) 0);
          [ rewrite Z.add_0_r; reflexivity
          | rewrite HX by lia; cbn [nth rm_saves snd]; symmetry; apply Z_to_bv_bv_unsigned ]
        | apply bv_unsigned_in_range ] end |]).
  destruct Hsr.
- replace (spZ regs - 112) with (spZ regs - 128 + 16) by lia.
  eapply (slot_of_region SEGS E' m _ _ _ _ _ _ _ e _ HR HU);
    [ unfold rm_frame; apply in_or_app; left; apply in_or_app; right; left; reflexivity
    | apply denot_lit_U | apply bv_unsigned_in_range ].
Qed.
(* the shadow-address register of the code's loops: Bx + (x + c) >> 3 *)
Lemma rm_reg_sh : forall (E' : env) nb nx b x c (w : word), ew E' nb = Z_to_bv 64 b -> ew E' nx = Z_to_bv 64 x ->
  0 <= b < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> b + (x + c) / 8 < 2 ^ 64 ->
  w = Z_to_bv 64 (b + (x + c) / 8) ->
  w = sv_denot E' (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SOff nx c) (SLit 3))).
Proof.
intros E' nb nx b x c w Hb Hx Rb Rx Rxc Rbx ->. rewrite (denot_lit_U E'). f_equal.
rewrite !U_SAlu, (U_atom E' nb b Hb Rb), U_SOff, Hx, unsigned_lit_small by lia. rewrite U_SLit.
rewrite (zcanon_id (x + c)) by (unfold M64; lia).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (x + c) 8 ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((x + c) / 8)) by (unfold M64; lia). symmetry. apply zcanon_id. unfold M64; lia.
Qed.


(* a member pj_get returned for the document, as rm_res (the node at the entry memory, in a cell of the kids block) *)
Lemma rm_res_of_get : forall lyc Wc memc mdc kc kname z,
  AJ STKrm (spZ regs) [] ly S Hp W mem md [] lyc S Hp Wc memc mdc kc -> ablocks B lyc S = ablocks B ly S ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam) doc t D ->
  prhPj_get_res (PA := PA) (mrestrict (w_H Wc) memc) (prh_lin Lam) doc t D kname z -> rm_res z.
Proof.
intros lyc Wc memc mdc kc kname z HJ Hbl Hn Hr.
destruct t as [| | | txt bits | sx | items | members]; cbn [prhPj_get_res] in Hr; try (left; exact Hr).
destruct Hr as [(_ & ->) | (i & v & kids & Di & Ei & _ & Hkd & -> & Hnz & Hinc)]; [left; reflexivity|].
cbn [pj_nodeR] in Hn.
destruct Hn as (_ & _ & num & str & kids' & keys & n & cap & Hh & _ & En & Hcn & Hcap & Di' & _ & _).
destruct Hh as (_ & _ & _ & _ & (Hk0' & Hk') & _).
destruct Hkd as (Hk0 & Hk).
pose proof (gs_val8_uniq _ _ _ _ Hk Hk' Hk0 Hk0') as Ekd. subst kids'.
assert (Hi : (i < length members)%nat) by (apply nth_error_Some; rewrite Ei; discriminate).
destruct Hcap as [(Hc0 & _) | (Hcp & Hlk & _)]; [lia|]. unfold prh_lin in Hlk.
right. exists v, Di, kids, cap, i. split; [|split; [exact Hlk | split; [reflexivity | lia]]].
apply (rm_node_move Wc W memc mem Lam _ v Di Hnz).
intros x Hx. destruct (rm_foot_lam _ Lam _ v Di kids cap (Z.of_nat i) Hnz Hlk eq_refl ltac:(lia) x Hx) as (a & k & Hin & Hax).
symmetry. pose proof HPRE as (HAR & _).
exact (rm_lam_kept ly S Hp W mem md Lam peak cnt fail ran most own lyc Wc memc mdc kc (spZ regs) HAR HLED HJ Hbl a k x Hin Hax).
Qed.
Lemma rm_tag5 : forall v, tag v = 5 -> exists items, v = JArr items.
Proof. intros v H. destruct v; cbn [tag] in H; try discriminate H. exists items. reflexivity. Qed.
(* the shadow-address register with the operands in the code's order: (x + c) >> 3 + Bx *)
Lemma rm_reg_sh2 : forall (E' : env) nb nx b x c (w : word), ew E' nb = Z_to_bv 64 b -> ew E' nx = Z_to_bv 64 x ->
  0 <= b < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> b + (x + c) / 8 < 2 ^ 64 ->
  w = Z_to_bv 64 (b + (x + c) / 8) ->
  w = sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff nx c) (SLit 3)) (SOff nb 0)).
Proof.
intros E' nb nx b x c w Hb Hx Rb Rx Rxc Rbx ->. rewrite (denot_lit_U E'). f_equal.
rewrite !U_SAlu, (U_atom E' nb b Hb Rb), U_SOff, Hx, unsigned_lit_small by lia. rewrite U_SLit.
rewrite (zcanon_id (x + c)) by (unfold M64; lia).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (x + c) 8 ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((x + c) / 8)) by (unfold M64; lia). symmetry. rewrite Z.add_comm. apply zcanon_id. unfold M64; lia.
Qed.

(* ---- the tail (AF_rm + 456 .. the return): pj_get_str (state, "encoding") and, when it is non-NULL,
   pj_get_str (state, "bytes"), then the epilogue ---- *)
Lemma rm_tail : forall lyL WL regsL memL mdL kL z2 seenv,
  rm_base lyL WL regsL memL mdL kL -> rm_res z2 ->
  0 <= seenv < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 112) 8 seenv ->
  getr regsL 8 = w64 z2 ->
  rm_goal WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 456))) memL (seg_rom SEGS)) mdL).
Proof.
intros lyL WL regsL memL mdL kL z2 seenv HB HZ2 Hsv0 Hsv R8.
destruct HB as (HJ & HPM & Eab & HLEDL & HFR & R2 & R3 & R4).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
pose proof HJ as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (SpL : spZ regsL = spZ regs - 128).
{ unfold spZ at 1. rewrite R2. apply unsigned_lit_small. lia. }
set (E := rm_EL regsL regs [seenv]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q =
  ew (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv])) q)
  by (intros q Hq; subst E; unfold rm_EL; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) =
  nth j0 (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv]) (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regsL) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_tail
  (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 456))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tail. apply pa_entry_st_ok_full.
  - subst E; unfold rm_EL. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rm_frame. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]. rewrite U2.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HPRS; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
      [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
          let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
        rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r;
        rewrite ?unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
        first [ exact Hsv0 | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
      | cbn; lia
      | change (N.to_nat 8) with 8%nat; rewrite SpL;
        first [ replace (spZ regs - 128 + 16) with (spZ regs - 112) by lia; exact Hsv
              | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                  apply (HFR (off, r)); cbn [rm_saves In]; tauto end ] ].
  - apply pairwise_disjoint_of_extents. unfold rm_frame, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [rm_sfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS RM_Bx [] E (mrestrict (w_H WL) memL)) by constructor.
assert (E243 : bv_unsigned (ew E 243) = VAL (A_OBJ 2)) by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold rm_goal.
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
(* ---- C8: pj_get_str (state, "encoding") at AF_rm + 468, returning to AF_rm + 472 ---- *)
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB.
pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b).
assert (U8 : bv_unsigned (ew E 8) = z2)
  by (rewrite (ER 8%nat 8%bv) by (lia || reflexivity); rewrite R8; unfold w64; apply unsigned_lit_small; lia).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (HspT : spZ (ms_regs ms) = spZ regs + -128) by (unfold spZ at 1; rewrite Q2, U2; lia).
gs_keep HFr U2 (spZ regs - 128) (spZ regs) K1. clear HF HG HFr.
assert (KL1 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H WL) (ms_mem ms) a = aview SEGS (w_H WL) memL a)
  by (intros a Ha; apply K1; lia).
pose proof HJ as (HAR1 & _).
pose proof (rm_ledger_keep lyL WL memL (ms_mem ms) _ HARL HLEDL KL1) as HLED1.
pose proof (rm_rod ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ HROD) as HROD1.
assert (Hin1 : In (VAL (A_OBJ 2) + 70016, 8) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
destruct (rm_key lyL S Hp WL (ms_mem ms) _ _ _ HAR1 HROD1 Hin1) as (l1 & Hl1len & HK1).
assert (HTOP1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyL).
{ destruct (rm_ly ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ) as (_ & _ & Ghi). rewrite Ghi. lia. }
assert (HRAZ1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 472)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
assert (HO1 : exists v Dz, z2 = 0 \/ pj_nodeR SEGS (mrestrict (w_H WL) (ms_mem ms)) (prh_lin Lam) z2 v Dz /\
    prhPj_rslot (PA := PA) B (STK_pj_get_str (PI := prh_img_A)) lyL S WL (ms_regs ms) (ms_mem ms) z2).
{ destruct (rm_res_at z2 lyL WL (ms_mem ms) _ kL (ms_regs ms) (STK_pj_get_str (PI := prh_img_A)) HZ2 HJ Eab ltac:(lia))
    as [Ez | (v & Dz & HN & HR)]; [exists t, D; left; exact Ez | exists v, Dz; right; split; assumption]. }
destruct HO1 as (v2 & Dz2 & HO1).
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs WL E _ ms STKrm (spZ regs) []
    ly S Hp W mem md [] lyL S Hp _ kL (STK_pj_get_str (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ).
  - exact HspT.
  - reflexivity.
  - lia.
  - exact FS5.
  - lia.
  - rewrite Q3, (ER 3%nat 3%bv) by (lia || reflexivity). rewrite R3. exact Hgp.
  - rewrite Q4, (ER 4%nat 4%bv) by (lia || reflexivity). rewrite R4. exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply rm_achain_low. unfold s0Z. rewrite Q8, U8. lia.
  - intros HPRE1.
    exact (PJ_GET_STR lyL S Hp WL (ms_regs ms) (ms_mem ms) _ [] z2 (VAL (A_OBJ 2) + 70016) l1 v2 Dz2 Lam peak cnt fail ran most own
      (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) ltac:(rewrite Q10, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity)
      ltac:(rewrite Q11, E243; reflexivity) HO1 HK1 HLED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk2 & -> & HJ2 & HJc2 & HP2 & HQ2).
destruct HQ2 as ((EHp2 & ES2 & Eab2 & HLED2 & HROOM2 & HRES2) & HKP2).
subst Hp2 S2. rewrite Eab in Eab2.
assert (HPM2 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by (intros h; exact (HKP2 (HPM h))).
clear HPM HKP2. rename HPM2 into HPM.
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?T -> _ => assert (HRK : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E);
    [exact HJc2 | exact HJ2 | exact U2 | lia | lia | lia | lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rename HS2 into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E 64 (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
remember (havoc E 64 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS, HEI2.
assert (OLD1 : forall q, (q < 64)%nat -> ew E1 q = ew E q) by (intros q Hq; rewrite HE1; apply ew_havoc_old; lia).
assert (U2a : bv_unsigned (ew E1 2) = spZ regsL) by (rewrite OLD1 by lia; exact U2).
assert (SHOK1 : sh_ok SEGS RM_Bx [] E1 (mrestrict (w_H W2) mem2)) by constructor.
clear SHOK HEI. rename SHOK1 into SHOK. rename HEI2 into HEI.
pose proof HJ2 as (HAR2 & _).
psrr_branch_tok RUN BR HS SHOK RM_span.
- (* C8 returned NULL: to the epilogue *)
  clear Hc. paj_run_tok_x_inv RUN HS HJ2 SHOK HPM RM_span; [gs_awr regsL U2a|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (MSF := msF) in * end.
  gs_keep HFr U2a (spZ regs - 128) (spZ regs) K2. clear HF HG HFr.
  assert (KL2 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem MSF) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; apply K2; lia).
  pose proof (rm_ledger_keep ly2 W2 mem2 (ms_mem MSF) _ HAR2 HLED2 KL2) as HLEDF.
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros matF.
  apply (rm_fin ly2 W2 (ms_regs MSF) (ms_mem MSF) _ matF _ regsL HJ2 HPM Eab2 HLEDF); [| | exact SpL].
  + intros r Hr. cbn [rm_allB map In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [rm_back HS OLD1 EX ER U2 SpL R3 R4 |]). destruct Hr.
  + rm_back HS OLD1 EX ER U2 SpL R3 R4.
- (* C8 returned a string: C9, pj_get_str (state, "bytes") at AF_rm + 488, returning to AF_rm + 492 *)
  clear Hc. paj_run_tok_x_inv RUN HS HJ2 SHOK HPM RM_span; [gs_awr regsL U2a|].
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (HspT2 : spZ (ms_regs ms0) = spZ regs + -128) by (unfold spZ at 1; rewrite P2, OLD1, U2 by lia; lia).
  gs_keep HFr U2a (spZ regs - 128) (spZ regs) K2. clear HF HG HFr.
  assert (KL2 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; apply K2; lia).
  pose proof (rm_ledger_keep ly2 W2 mem2 (ms_mem ms0) _ HAR2 HLED2 KL2) as HLED3.
  pose proof HJ2 as (HAR3 & _).
  pose proof (rm_rod ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ2 HROD) as HROD3.
  assert (Hin2 : In (VAL (A_OBJ 2) + 70048, 5) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
  destruct (rm_key ly2 S Hp W2 (ms_mem ms0) _ _ _ HAR3 HROD3 Hin2) as (l2 & Hl2len & HK2).
  assert (HTOP2 : spZ (ms_regs ms0) + 64 <= ly_stk_hi ly2).
  { destruct (rm_ly ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ2) as (_ & _ & Ghi). rewrite Ghi. lia. }
  assert (HRAZ2 : raZ (ms_regs ms0) < YM05.alloc_ceiling).
  { pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 492)
      ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
    rewrite EAF in HSL. unfold raZ. rewrite P1, unsigned_lit_small by lia. lia. }
  assert (HO2 : exists v Dz, z2 = 0 \/ pj_nodeR SEGS (mrestrict (w_H W2) (ms_mem ms0)) (prh_lin Lam) z2 v Dz /\
      prhPj_rslot (PA := PA) B (STK_pj_get_str (PI := prh_img_A)) ly2 S W2 (ms_regs ms0) (ms_mem ms0) z2).
  { destruct (rm_res_at z2 ly2 W2 (ms_mem ms0) _ _ (ms_regs ms0) (STK_pj_get_str (PI := prh_img_A)) HZ2 HJ2 Eab2
      ltac:(lia)) as [Ez | (v & Dz & HN & HR)]; [exists t, D; left; exact Ez | exists v, Dz; right; split; assumption]. }
  destruct HO2 as (v3 & Dz3 & HO2).
  assert (E1_243 : bv_unsigned (ew E1 243) = VAL (A_OBJ 2)) by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  eapply SRr_bind.
  { eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W2 E1 _ ms0 STKrm (spZ regs) []
      ly S Hp W mem md [] ly2 S Hp _ _ (STK_pj_get_str (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ2).
    - exact HspT2.
    - reflexivity.
    - lia.
    - exact FS5.
    - lia.
    - rewrite P3, OLD1, (ER 3%nat 3%bv) by (lia || reflexivity). rewrite R3. exact Hgp.
    - rewrite P4, OLD1, (ER 4%nat 4%bv) by (lia || reflexivity). rewrite R4. exact Htp.
    - exact P1.
    - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply rm_achain_low. unfold s0Z. rewrite P8, OLD1, U8 by lia. lia.
    - intros HPRE2.
      exact (PJ_GET_STR ly2 S Hp W2 (ms_regs ms0) (ms_mem ms0) _ [] z2 (VAL (A_OBJ 2) + 70048) l2 v3 Dz3 Lam peak cnt fail ran
        most own (conj HPRE2 (conj HROD3 (conj HTOP2 (conj HRAZ2 HFRM))))
        ltac:(rewrite P10, OLD1, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity)
        ltac:(rewrite P11, E1_243; reflexivity) HO2 HK2 HLED3).
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & kk3 & -> & HJ3 & HJc3 & HP3 & HQ3).
  destruct HQ3 as ((EHp3 & ES3 & Eab3 & HLED4 & HROOM3 & HRES3) & HKP3).
  subst Hp3 S3. rewrite Eab2 in Eab3.
  assert (HPM3 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3) by (intros h; exact (HKP3 (HPM h))).
  clear HPM HKP3. rename HPM3 into HPM.
  jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
  lazymatch type of HS3 with ?T -> _ => assert (HRK : T) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E1);
      [exact HJc3 | exact HJ3 | exact U2a | lia | lia | lia | lia | lia]. }
  specialize (HS3 HRK). clear HRK HS. rename HS3 into HS.
  rewrite <- restrict_mkst_fx in HS.
  pose proof (img_env_havoc (PI := PA) E1 80 (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
  remember (havoc E1 80 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS, HEI3.
  assert (OLD2 : forall q, (q < 64)%nat -> ew E2 q = ew E q)
    by (intros q Hq; rewrite HE2, ew_havoc_old by lia; apply OLD1; lia).
  assert (U2b : bv_unsigned (ew E2 2) = spZ regsL) by (rewrite OLD2 by lia; exact U2).
  assert (SHOK3 : sh_ok SEGS RM_Bx [] E2 (mrestrict (w_H W3) mem3)) by constructor.
  clear SHOK HEI. rename SHOK3 into SHOK. rename HEI3 into HEI.
  pose proof HJ3 as (HAR4 & _).
  paj_run_tok_x_inv RUN HS HJ3 SHOK HPM RM_span; [gs_awr regsL U2b|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (MSF := msF) in * end.
  gs_keep HFr U2b (spZ regs - 128) (spZ regs) K3. clear HF HG HFr.
  assert (KL3 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W3) (ms_mem MSF) a = aview SEGS (w_H W3) mem3 a)
    by (intros a Ha; apply K3; lia).
  pose proof (rm_ledger_keep ly3 W3 mem3 (ms_mem MSF) _ HAR4 HLED4 KL3) as HLEDF.
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros matF.
  apply (rm_fin ly3 W3 (ms_regs MSF) (ms_mem MSF) _ matF _ regsL HJ3 HPM Eab3 HLEDF); [| | exact SpL].
  + intros r Hr. cbn [rm_allB map In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [rm_back HS OLD2 EX ER U2 SpL R3 R4 |]). destruct Hr.
  + rm_back HS OLD2 EX ER U2 SpL R3 R4.

Qed.
(* the item counter the loop keeps in s9 (i - 1, then i after its increment) *)
Lemma rm_U_pred : forall (E' : env) q (i : nat), ew E' q = Z_to_bv 64 (Z.of_nat i - 1) -> Z.of_nat i < 2 ^ 64 ->
  U E' (SOff q 1) = Z.of_nat i.
Proof.
intros E' q i H Hi. rewrite U_SOff, H, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia.
replace (Z.of_nat i - 1 + 1) with (Z.of_nat i) by lia. apply Z.mod_small. lia.
Qed.

(* a register of a later state, against the seat's env E (AG : env_agree 64 E Ex, the havocs since) *)
Ltac rm_lreg HS AG :=
  lazymatch goal with |- getr _ ?r = _ =>
    let G := fresh "G" in
    pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
    lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end;
    rewrite G; clear G; try (rewrite (sv_denot_agree 64 _ _ _ AG) by reflexivity)
  end.
(* a register at a call (the state is st_ok at the callee's entry), as an expression over the env *)
Ltac rm_creg HS r G :=
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H Ex ss ms r HS) as G;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in G;
    cbn [ms_regs restrict mkst] in G
  end.
(* the ledger across a stretch whose only write window is the frame's [sp + 8, sp + 24) *)
Ltac rm_led_keep HFr U2x HARx HLEDx HLEDy :=
  lazymatch type of HFr with frame_of _ _ (mrestrict (w_H ?Wx) ?m) (mrestrict (w_H _) ?m') =>
  let K := fresh "K" in let KL := fresh "KL" in
  gs_keep HFr U2x (spZ regs - 120) (spZ regs - 104) K;
  assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a)
    by (intros a Ha; apply K; lia);
  lazymatch type of HLEDx with prh_ledger _ ?lyx _ _ _ _ _ _ _ _ _ _ _ =>
    pose proof (rm_ledger_keep lyx Wx m m' _ HARx HLEDx KL) as HLEDy end;
  clear K KL end.
(* the frame facts at a seat's state HS (region 0 is the frame), with its sp and saved-register atoms *)
Ltac rm_frame_at HS U2x EXSx HFRx Hsvx :=
  let RG := fresh "RG" in
  pose proof (st_ok_region_nth SEGS _ _ _ 0 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG;
  lazymatch type of RG with
  | region_ok ?sg ?Ex ?mx (YP09.mkRegion _ _ _ _ _ (YP09.mkChunk 16 (CVal 8 ?e) :: _)) =>
      change (region_ok sg Ex mx (rm_frame ([] ++ [YP09.mkChunk 16 (CVal 8 e)]))) in RG
  | region_ok ?sg ?Ex ?mx (YP09.mkRegion _ _ _ _ _ (?c8 :: YP09.mkChunk 16 (CVal 8 ?e) :: _)) =>
      change (region_ok sg Ex mx (rm_frame ([c8] ++ [YP09.mkChunk 16 (CVal 8 e)]))) in RG
  end;
  destruct (rm_frame_facts _ _ _ _ RG U2x EXSx) as (HFRx & Hsvx); clear RG.

(* ---- the params loop (AF_rm + 328 ..): per item, pj_get_str (&kids[i], "symbol") and, when it is non-NULL,
   pj_get (&kids[i], "value"); by induction on the items left; the exit is the tail ---- *)
Lemma rm_ploop : forall (k i : nat) lyL WL regsL memL mdL kL z2 seenv z1 items Dz1 kd cd j1,
  (length items - i = k)%nat -> (i <= length items)%nat ->
  rm_base lyL WL regsL memL mdL kL -> rm_res z2 ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) z1 (JArr items) Dz1 ->
  In (kd, 56 * cd) Lam -> z1 = kd + 56 * Z.of_nat j1 -> Z.of_nat j1 < cd ->
  0 <= seenv < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 112) 8 seenv ->
  getr regsL 8 = w64 z2 -> getr regsL 9 = w64 z1 -> getr regsL 18 = w64 (z1 + 24) -> getr regsL 19 = w64 (z1 + 40) ->
  getr regsL 20 = w64 (VAL (A_OBJ 2) + 69952) -> getr regsL 21 = w64 (VAL (A_OBJ 2) + 69984) ->
  getr regsL 22 = w64 (SHADOW_OFF + z1 / 8) -> getr regsL 23 = w64 5 ->
  getr regsL 24 = w64 (56 * Z.of_nat i) -> getr regsL 25 = w64 (Z.of_nat i - 1) ->
  getr regsL 26 = w64 (SHADOW_OFF + (z1 + 40) / 8) -> getr regsL 27 = w64 (SHADOW_OFF + (z1 + 24) / 8) ->
  rm_goal WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 328))) memL (seg_rom SEGS)) mdL).
Proof.
intros k. induction k as [k IH] using lt_wf_ind.
intros i lyL WL regsL memL mdL kL z2 seenv z1 items Dz1 kd cd j1 Hk Hi HB HZ2 HZ1 Hkd Ez1 Hj1
  Hsv0 Hsv R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
pose proof HB as (HJ & HPM & Eab & HLEDL & HFR & R2 & R3 & R4).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
pose proof HJ as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (SpL : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB0.
pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b).
pose proof (rm_cell_low kd cd (Z.of_nat j1) Hkd ltac:(lia)) as (Z1a & Z1b). rewrite <- Ez1 in Z1a, Z1b.
(* params: an array node in a cell of a ledger block; its header at the current memory *)
pose proof HZ1 as HZ1'. cbn [pj_nodeR] in HZ1'.
destruct HZ1' as (_ & _ & num1 & str1 & kids1 & keys1 & n1 & cap1 & Hh1 & Es1 & Ek1 & En1 & Hcn1 & Hcap1 & Di1 & ED1 & HIt).
cbn [tag] in Hh1.
destruct Hh1 as ((Hal8 & _) & (Hty0 & Hty) & _ & _ & (Hkd0 & Hkdv) & _ & (Hn0 & Hnv) & _).
assert (KV : forall a n v, z1 <= a -> a + Z.of_nat n <= z1 + 56 ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H WL) memL) a n v).
{ intros a n v H1 H2 Hv. apply (rm_val_lam lyL WL memL mdL kL kd cd a n v HJ Eab Hkd); [lia | lia | exact Hv]. }
(* ---- the seat ---- *)
set (E := rm_EL regsL regs [seenv; n1; kids1]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q =
  ew (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; n1; kids1])) q)
  by (intros q Hq; subst E; unfold rm_EL; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) =
  nth j0 (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; n1; kids1])
    (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (EXS : forall j0, (j0 < 13)%nat -> ew E (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv)))).
{ intros j0 Hj0. change (33 + j0)%nat with (32 + Datatypes.S j0)%nat. rewrite EX by (unfold A_TEXT; lia).
  cbn [nth]. rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr regs (snd (0, 0%bv)))) by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun sr => getr regs (snd sr))). reflexivity. }
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regsL) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 seenv) by (change 46%nat with (32 + 14)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E47 : ew E 47 = Z_to_bv 64 n1) by (change 47%nat with (32 + 15)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E48 : ew E 48 = Z_to_bv 64 kids1) by (change 48%nat with (32 + 16)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 z1) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (U9 : bv_unsigned (ew E 9) = z1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E243 : bv_unsigned (ew E 243) = VAL (A_OBJ 2)) by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_loop
  (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 328))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_loop. apply pa_entry_st_ok_full.
  - unfold rm_lregs.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [subst E; unfold rm_EL; apply regs_ok_Eimg_Ereg | |] | |] | |] | |] | |] | |]; try (intros X; discriminate X).
    + rewrite R18. symmetry. apply gs_denot_off. exact E9.
    + rewrite R19. symmetry. apply gs_denot_off. exact E9.
    + rewrite R22. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 0); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | unfold w64; rewrite Z.add_0_r; reflexivity].
    + rewrite R23. reflexivity.
    + rewrite R26. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 40); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
    + rewrite R27. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 24); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
  - vm_compute. reflexivity.
  - unfold rm_frame, rm_node. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]; rewrite ?U2, ?U9.
    + split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRS; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
        [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
            let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
          rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r;
          rewrite ?unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
          first [ exact Hsv0 | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
        | cbn; lia
        | change (N.to_nat 8) with 8%nat; rewrite SpL;
          first [ replace (spZ regs - 128 + 16) with (spZ regs - 112) by lia; exact Hsv
                | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                    apply (HFR (off, r)); cbn [rm_saves In]; tauto end ] ].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ z1 0 4 (SLit 5) 5); [reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply KV; [lia | cbn; lia | exact Hty].
      * apply (chunk_ok_val SEGS E _ z1 24 8 (SOff 48 0) kids1);
          [rewrite (gs_denot_off E 48 kids1 0 E48), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        apply KV; [lia | cbn; lia | exact Hkdv].
      * apply (chunk_ok_val SEGS E _ z1 40 8 (SOff 47 0) n1);
          [rewrite (gs_denot_off E 47 n1 0 E47), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        apply KV; [lia | cbn; lia | exact Hnv].
  - apply pairwise_disjoint_of_extents. unfold rm_frame, rm_node, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [rm_sfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS RM_Bx RM_SHN E (mrestrict (w_H WL) memL))
  by exact (rm_shok_node E lyL WL memL mdL kL z1 kd cd j1 HJ Eab Hkd Ez1 Hj1 E32 E9).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
unfold rm_goal.
(* the n word, i = s9 + 1, the bound test *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
assert (U2' : bv_unsigned (ew E 2) = spZ regs - 128) by lia.
pose proof HJ as (HARx & _).
rm_led_keep HFr U2 HARL HLEDL HLED1. clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK RM_span.
- (* taken: i >= n, the loop is done: the tail *)
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM RM_span (AF_rm + 456); [gs_awr regsL U2|].
  rm_led_keep HFr U2 HARx HLED1 HLED2. clear HF HG HFr.
  rm_frame_at HS U2' EXS HFR1 Hsv1.
  prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4. prreg HS (8%bv : bv 5) G8.
  pmkst HS. replace (BASE + 4576) with (BASE + (AF_rm + 456)) by (rewrite EAF; reflexivity).
  apply (rm_tail lyL WL (ms_regs ms0) (ms_mem ms0) _ kL z2 (U E (SOff 46 0))).
  + split; [exact HJ|]. split; [exact HPM|]. split; [exact Eab|]. split; [exact HLED2|]. split; [exact HFR1|].
    split; [rewrite G2, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
    split; [rewrite G3, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
    rewrite G4, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + exact HZ2.
  + unfold U. apply bv_unsigned_in_range.
  + exact Hsv1.
  + rewrite G8, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
- (* not taken: item i *)
  rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (rm_U_pred E 25 i) in Hc by (try (rewrite (ER 25%nat 25%bv) by (lia || reflexivity); exact R25); lia).
  rewrite (U_atom E 47 n1 E47) in Hc by lia. rewrite En1 in Hc. rename Hc into Hilt.
  destruct (nth_error items i) as [u|] eqn:Eu; [|apply nth_error_None in Eu; lia].
  destruct Hcap1 as [(Hc0 & _) | (Hcp1 & Hlk1)]; [lia|]. unfold prh_lin in Hlk1.
  destruct (rm_items_nth _ items kids1 Di1 i u HIt Eu) as (Du & HU).
  assert (HRI : rm_res (kids1 + 56 * Z.of_nat i)) by (right; exists u, Du, kids1, cap1, i; repeat split; auto; lia).
  pose proof (rm_res_low _ HRI) as (I1 & I2).
  assert (AG0 : env_agree 64 E E) by apply env_agree_refl.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
  rm_led_keep HFr U2 HARx HLED1 HLED2. clear HF HG HFr.
  pose proof HJ as (HAR6 & _).
  (* ---- C6: pj_get_str (&kids[i], "symbol") at AF_rm + 368, returning to AF_rm + 372 ---- *)
  prreg HS (1%bv : bv 5) Q16. rm_creg HS (2%bv : bv 5) Q26. rm_creg HS (3%bv : bv 5) Q36.
  rm_creg HS (4%bv : bv 5) Q46. rm_creg HS (8%bv : bv 5) Q86. rm_creg HS (10%bv : bv 5) Q106.
  rm_creg HS (11%bv : bv 5) Q116.
  try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q26 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q36 by reflexivity).
  try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q46 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q86 by reflexivity).
  try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q106 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q116 by reflexivity).
  assert (HspT6 : spZ (ms_regs ms0) = spZ regs + -128)
    by (unfold spZ at 1; rewrite Q26; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U2; lia).
  pose proof (rm_rod ly S Hp W mem md lyL S Hp WL (ms_mem ms0) _ _ (spZ regs) HJ HROD) as HROD6.
  assert (Hin6 : In (VAL (A_OBJ 2) + 69952, 6) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
  destruct (rm_key lyL S Hp WL (ms_mem ms0) _ _ _ HAR6 HROD6 Hin6) as (lk6 & Hlk6 & HK6).
  assert (HTOP6 : spZ (ms_regs ms0) + 64 <= ly_stk_hi lyL).
  { destruct (rm_ly ly S Hp W mem md lyL S Hp WL (ms_mem ms0) _ _ (spZ regs) HJ) as (_ & _ & Ghi). rewrite Ghi. lia. }
  assert (HRAZ6 : raZ (ms_regs ms0) < YM05.alloc_ceiling).
  { pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 372)
      ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
    rewrite EAF in HSL. unfold raZ. rewrite Q16, unsigned_lit_small by lia. lia. }
  assert (HO6 : exists v Dz, kids1 + 56 * Z.of_nat i = 0 \/
      pj_nodeR SEGS (mrestrict (w_H WL) (ms_mem ms0)) (prh_lin Lam) (kids1 + 56 * Z.of_nat i) v Dz /\
      prhPj_rslot (PA := PA) B (STK_pj_get_str (PI := prh_img_A)) lyL S WL (ms_regs ms0) (ms_mem ms0) (kids1 + 56 * Z.of_nat i)).
  { destruct (rm_res_at _ lyL WL (ms_mem ms0) _ _ (ms_regs ms0) (STK_pj_get_str (PI := prh_img_A)) HRI HJ Eab ltac:(lia))
      as [Ez | (v & Dz & HN & HR)]; [exists t, D; left; exact Ez | exists v, Dz; right; split; assumption]. }
  destruct HO6 as (vo6 & Do6 & HO6).
  eapply SRr_bind.
  { eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs WL E _ ms0 STKrm (spZ regs) []
      ly S Hp W mem md [] lyL S Hp _ _ (STK_pj_get_str (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ).
    - exact HspT6.
    - reflexivity.
    - lia.
    - exact FS5.
    - lia.
    - rewrite Q36. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv) by (lia || reflexivity).
      rewrite R3. exact Hgp.
    - rewrite Q46. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv) by (lia || reflexivity).
      rewrite R4. exact Htp.
    - exact Q16.
    - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply rm_achain_low. unfold s0Z. rewrite Q86. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity).
      unfold w64. rewrite unsigned_lit_small by lia. lia.
    - intros HPRE6.
      refine (PJ_GET_STR lyL S Hp WL (ms_regs ms0) (ms_mem ms0) _ [] (kids1 + 56 * Z.of_nat i) (VAL (A_OBJ 2) + 69952) lk6
        vo6 Do6 Lam peak cnt fail ran most own (conj HPRE6 (conj HROD6 (conj HTOP6 (conj HRAZ6 HFRM)))) _ _ HO6
        HK6 HLED2).
      + rewrite Q106, denot_lit_U. unfold w64. f_equal. rewrite U_SAlu.
        rewrite (U_atom E 24 (56 * Z.of_nat i)) by (first [rewrite (ER 24%nat 24%bv), R24 by (lia || reflexivity); reflexivity | lia]).
        rewrite (U_atom E 48 kids1 E48) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      + rewrite Q116. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 20%nat 20%bv) by (lia || reflexivity).
        exact R20.
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W2 c6 Hwle6 (ly2 & S6 & Hp6 & regs6 & mem2 & md6 & kk6 & -> & HJ6 & HJc6 & HP6 & HQ6).
  destruct HQ6 as ((EHp6 & ES6 & Eab6 & HLED6 & HROOM6 & HRES6) & HKP6).
  subst Hp6 S6. rewrite Eab in Eab6.
  assert (HPMn : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by (intros h; exact (HKP6 (HPM h))).
  clear HPM HKP6. rename HPMn into HPM.
  jafter_call_keep_pi HS 64%nat regs6 (mrestrict (w_H W2) mem2) HP6 [0; 1]%nat HSn.
  lazymatch type of HSn with ?T -> _ => assert (HRK : T) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E);
        [exact HJc6 | exact HJ6 | try (rewrite (proj1 AG0 2%nat) by lia); exact U2 | lia | lia | lia | lia | lia].
    - eapply (rm_node_kept E z1 kd cd j1 _ _ lyL WL _ _ ly2 W2 mem2 md6 _ _ HJc6 HAR6 Eab Eab6 Hkd Ez1 Hj1).
      try (rewrite (proj1 AG0 9%nat) by lia). exact U9. }
  specialize (HSn HRK). clear HRK HS. rename HSn into HS.
  rewrite <- restrict_mkst_fx in HS.
  pose proof (img_env_havoc (PI := PA) E 64 (map (getr regs6) CLOB) HEI ltac:(cbv; lia)) as HEIn.
  remember (havoc E 64 (map (getr regs6) CLOB)) as E1 eqn:HE6 in HS, HEIn.
  assert (AG1 : env_agree 64 E E1) by (rewrite HE6; apply env_agree_havoc_ge; [lia | exact AG0]).
  assert (U2a : bv_unsigned (ew E1 2) = spZ regsL) by (rewrite (proj1 AG1 2%nat) by lia; exact U2).
  assert (SHOKn : sh_ok SEGS RM_Bx RM_SHN E1 (mrestrict (w_H W2) mem2)).
  { apply (rm_shok_node E1 ly2 W2 mem2 _ _ z1 kd cd j1 HJ6 Eab6 Hkd Ez1 Hj1);
      rewrite (proj1 AG1 _) by lia; [exact E32 | exact E9]. }
  clear SHOK HEI. rename SHOKn into SHOK. rename HEIn into HEI.
  pose proof HJ6 as (HAR7 & _).
  psrr_branch_tok RUN BR HS SHOK RM_span.
  + (* C6 returned NULL: the seen update, the back edge *)
    clear Hc. paj_run_to_tok_x_inv RUNTO HS HJ6 SHOK HPM RM_span (AF_rm + 328); [gs_awr regsL U2a|].
    rm_led_keep HFr U2a HAR7 HLED6 HLEDB. clear HF HG HFr.
    assert (U2B : bv_unsigned (ew E1 2) = spZ regs - 128)
      by (rewrite (proj1 AG1 2%nat) by lia; lia).
    assert (EXSB : forall j0, (j0 < 13)%nat -> ew E1 (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv))))
      by (intros j0 Hj0; rewrite (proj1 AG1 (33 + j0)%nat) by lia; apply EXS; exact Hj0).
    rm_frame_at HS U2B EXSB HFRB HsvB.
    pmkst HS. replace (BASE + 4448) with (BASE + (AF_rm + 328)) by (rewrite EAF; reflexivity).
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdB) _ =>
      eapply (IH (length items - Datatypes.S i)%nat ltac:(lia) (Datatypes.S i) ly2 W2 (ms_regs ms1) (ms_mem ms1) mdB _ z2
        _ z1 items Dz1 kd cd j1 eq_refl ltac:(lia)) end.
    all: try (exact HZ2 || exact HZ1 || exact Hkd || exact Ez1 || exact Hj1 || exact HsvB).
    * split; [exact HJ6|]. split; [exact HPM|]. split; [exact Eab6|]. split; [exact HLEDB|]. split; [exact HFRB|].
      split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
      split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
      rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
    * unfold U. apply bv_unsigned_in_range.
    * rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG1. rewrite (gs_denot_off E 9 z1 24 E9). reflexivity.
    * rm_lreg HS AG1. rewrite (gs_denot_off E 9 z1 40 E9). reflexivity.
    * rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 20%nat 20%bv), R20 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 21%nat 21%bv), R21 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG1. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 0); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | unfold w64; rewrite Z.add_0_r; reflexivity].
    * rm_lreg HS AG1. reflexivity.
    * rm_lreg HS AG1. rewrite (gs_denot_off E 24 (56 * Z.of_nat i) 56)
        by (rewrite (ER 24%nat 24%bv), R24 by (lia || reflexivity); reflexivity).
      unfold w64. f_equal. lia.
    * rm_lreg HS AG1. cbn [sv_denot]. rewrite (ER 25%nat 25%bv), R25 by (lia || reflexivity). unfold w64.
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
    * rm_lreg HS AG1. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 40); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
    * rm_lreg HS AG1. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 24); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
  + (* C6 returned a string: C7, pj_get (&kids[i], "value") at AF_rm + 396, returning to AF_rm + 400 *)
    clear Hc. paj_run_tok_x_inv RUN HS HJ6 SHOK HPM RM_span; [gs_awr regsL U2a|].
    rm_led_keep HFr U2a HAR7 HLED6 HLED6k. clear HF HG HFr.
    pose proof HJ6 as (HAR8 & _).
    prreg HS (1%bv : bv 5) Q17. rm_creg HS (2%bv : bv 5) Q27. rm_creg HS (3%bv : bv 5) Q37.
    rm_creg HS (4%bv : bv 5) Q47. rm_creg HS (8%bv : bv 5) Q87. rm_creg HS (10%bv : bv 5) Q107.
    rm_creg HS (11%bv : bv 5) Q117.
    try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q27 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q37 by reflexivity).
    try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q47 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q87 by reflexivity).
    try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q107 by reflexivity). try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q117 by reflexivity).
    assert (HspT7 : spZ (ms_regs ms1) = spZ regs + -128)
      by (unfold spZ at 1; rewrite Q27; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U2; lia).
    pose proof (rm_rod ly S Hp W mem md ly2 S Hp W2 (ms_mem ms1) _ _ (spZ regs) HJ6 HROD) as HROD7.
    assert (Hin7 : In (VAL (A_OBJ 2) + 69984, 5) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
    destruct (rm_key ly2 S Hp W2 (ms_mem ms1) _ _ _ HAR8 HROD7 Hin7) as (lk7 & Hlk7 & HK7).
    assert (HTOP7 : spZ (ms_regs ms1) + 64 <= ly_stk_hi ly2).
    { destruct (rm_ly ly S Hp W mem md ly2 S Hp W2 (ms_mem ms1) _ _ (spZ regs) HJ6) as (_ & _ & Ghi). rewrite Ghi. lia. }
    assert (HRAZ7 : raZ (ms_regs ms1) < YM05.alloc_ceiling).
    { pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 400)
        ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
      rewrite EAF in HSL. unfold raZ. rewrite Q17, unsigned_lit_small by lia. lia. }
    assert (HO7 : exists v Dz, kids1 + 56 * Z.of_nat i = 0 \/
        pj_nodeR SEGS (mrestrict (w_H W2) (ms_mem ms1)) (prh_lin Lam) (kids1 + 56 * Z.of_nat i) v Dz /\
        prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_A)) ly2 S W2 (ms_regs ms1) (ms_mem ms1) (kids1 + 56 * Z.of_nat i)).
    { destruct (rm_res_at _ ly2 W2 (ms_mem ms1) _ _ (ms_regs ms1) (STK_pj_get (PI := prh_img_A)) HRI HJ6 Eab6 ltac:(lia))
        as [Ez | (v & Dz & HN & HR)]; [exists t, D; left; exact Ez | exists v, Dz; right; split; assumption]. }
    destruct HO7 as (vo7 & Do7 & HO7).
    eapply SRr_bind.
    { eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W2 E1 _ ms1 STKrm (spZ regs) []
        ly S Hp W mem md [] ly2 S Hp _ _ (STK_pj_get (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ6).
      - exact HspT7.
      - reflexivity.
      - lia.
      - exact FS4.
      - lia.
      - rewrite Q37. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv) by (lia || reflexivity).
        rewrite R3. exact Hgp.
      - rewrite Q47. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv) by (lia || reflexivity).
        rewrite R4. exact Htp.
      - exact Q17.
      - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
      - rewrite unsigned_lit_small by lia. lia.
      - apply rm_achain_low. unfold s0Z. rewrite Q87. cbn [sv_denot].
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity).
        unfold w64. rewrite unsigned_lit_small by lia. lia.
      - intros HPRE7.
        refine (PJ_GET ly2 S Hp W2 (ms_regs ms1) (ms_mem ms1) _ [] (kids1 + 56 * Z.of_nat i) (VAL (A_OBJ 2) + 69984) lk7
          vo7 Do7 Lam peak cnt fail ran most own (conj HPRE7 (conj HROD7 (conj HTOP7 (conj HRAZ7 HFRM)))) _ _ HO7
          HK7 HLED6k).
        + rewrite Q107, denot_lit_U. unfold w64. f_equal. rewrite U_SAlu.
          rewrite (U_atom E 24 (56 * Z.of_nat i)) by (first [rewrite (ER 24%nat 24%bv), R24 by (lia || reflexivity); reflexivity | lia]).
          rewrite (U_atom E 48 kids1 E48) by lia.
          cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
        + rewrite Q117. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 21%nat 21%bv) by (lia || reflexivity).
          exact R21.
      - intros a (r & Hr & _). destruct Hr. }
    cbv beta. intros W3 c7 Hwle7 (ly3 & S7 & Hp7 & regs7 & mem3 & md7 & kk7 & -> & HJ7 & HJc7 & HP7 & HQ7).
    destruct HQ7 as ((EHp7 & ES7 & Eab7 & HLED7 & HROOM7 & HRES7) & HKP7).
    subst Hp7 S7. rewrite Eab6 in Eab7.
    assert (HPMn : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3) by (intros h; exact (HKP7 (HPM h))).
    clear HPM HKP7. rename HPMn into HPM.
    jafter_call_keep_pi HS 80%nat regs7 (mrestrict (w_H W3) mem3) HP7 [0; 1]%nat HSn.
    lazymatch type of HSn with ?T -> _ => assert (HRK : T) end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E1);
          [exact HJc7 | exact HJ7 | try (rewrite (proj1 AG1 2%nat) by lia); exact U2 | lia | lia | lia | lia | lia].
      - eapply (rm_node_kept E1 z1 kd cd j1 _ _ ly2 W2 _ _ ly3 W3 mem3 md7 _ _ HJc7 HAR8 Eab6 Eab7 Hkd Ez1 Hj1).
        try (rewrite (proj1 AG1 9%nat) by lia). exact U9. }
    specialize (HSn HRK). clear HRK HS. rename HSn into HS.
    rewrite <- restrict_mkst_fx in HS.
    pose proof (img_env_havoc (PI := PA) E1 80 (map (getr regs7) CLOB) HEI ltac:(cbv; lia)) as HEIn.
    remember (havoc E1 80 (map (getr regs7) CLOB)) as E2 eqn:HE7 in HS, HEIn.
    assert (AG2 : env_agree 64 E E2) by (rewrite HE7; apply env_agree_havoc_ge; [lia | exact AG1]).
    assert (U2b : bv_unsigned (ew E2 2) = spZ regsL) by (rewrite (proj1 AG2 2%nat) by lia; exact U2).
    assert (SHOKn : sh_ok SEGS RM_Bx RM_SHN E2 (mrestrict (w_H W3) mem3)).
    { apply (rm_shok_node E2 ly3 W3 mem3 _ _ z1 kd cd j1 HJ7 Eab7 Hkd Ez1 Hj1);
        rewrite (proj1 AG2 _) by lia; [exact E32 | exact E9]. }
    clear SHOK HEI. rename SHOKn into SHOK. rename HEIn into HEI.
    pose proof HJ7 as (HAR9 & _).
    paj_run_to_tok_x_inv RUNTO HS HJ7 SHOK HPM RM_span (AF_rm + 328); [gs_awr regsL U2b|].
    rm_led_keep HFr U2b HAR9 HLED7 HLEDB. clear HF HG HFr.
    assert (U2B : bv_unsigned (ew E2 2) = spZ regs - 128)
      by (rewrite (proj1 AG2 2%nat) by lia; lia).
    assert (EXSB : forall j0, (j0 < 13)%nat -> ew E2 (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv))))
      by (intros j0 Hj0; rewrite (proj1 AG2 (33 + j0)%nat) by lia; apply EXS; exact Hj0).
    rm_frame_at HS U2B EXSB HFRB HsvB.
    pmkst HS. replace (BASE + 4448) with (BASE + (AF_rm + 328)) by (rewrite EAF; reflexivity).
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdB) _ =>
      eapply (IH (length items - Datatypes.S i)%nat ltac:(lia) (Datatypes.S i) ly3 W3 (ms_regs ms2) (ms_mem ms2) mdB _ z2
        _ z1 items Dz1 kd cd j1 eq_refl ltac:(lia)) end.
    all: try (exact HZ2 || exact HZ1 || exact Hkd || exact Ez1 || exact Hj1 || exact HsvB).
    * split; [exact HJ7|]. split; [exact HPM|]. split; [exact Eab7|]. split; [exact HLEDB|]. split; [exact HFRB|].
      split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
      split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
      rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
    * unfold U. apply bv_unsigned_in_range.
    * rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG2. rewrite (gs_denot_off E 9 z1 24 E9). reflexivity.
    * rm_lreg HS AG2. rewrite (gs_denot_off E 9 z1 40 E9). reflexivity.
    * rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 20%nat 20%bv), R20 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 21%nat 21%bv), R21 by (lia || reflexivity); reflexivity.
    * rm_lreg HS AG2. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 0); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | unfold w64; rewrite Z.add_0_r; reflexivity].
    * rm_lreg HS AG2. reflexivity.
    * rm_lreg HS AG2. rewrite (gs_denot_off E 24 (56 * Z.of_nat i) 56)
        by (rewrite (ER 24%nat 24%bv), R24 by (lia || reflexivity); reflexivity).
      unfold w64. f_equal. lia.
    * rm_lreg HS AG2. cbn [sv_denot]. rewrite (ER 25%nat 25%bv), R25 by (lia || reflexivity). unfold w64.
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
    * rm_lreg HS AG2. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 40); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
    * rm_lreg HS AG2. symmetry. eapply (rm_reg_sh E 32 9 SHADOW_OFF z1 24); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia | lia
        | unfold SHADOW_OFF; lia | reflexivity].
Qed.

(* ---- params' type check (AF_rm + 240 ..): its shadow (the node, LAWS' field 14), the type word; an array enters the
   params loop at item 0, anything else goes to the tail ---- *)
Lemma rm_pentry : forall lyL WL regsL memL mdL kL z2 seenv z1 v Dz1 kd cd j1,
  rm_base lyL WL regsL memL mdL kL -> rm_res z2 ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) z1 v Dz1 ->
  In (kd, 56 * cd) Lam -> z1 = kd + 56 * Z.of_nat j1 -> Z.of_nat j1 < cd ->
  0 <= seenv < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 112) 8 seenv ->
  getr regsL 8 = w64 z2 -> getr regsL 9 = w64 z1 -> getr regsL 20 = w64 SHADOW_OFF ->
  rm_goal WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 240))) memL (seg_rom SEGS)) mdL).
Proof.
intros lyL WL regsL memL mdL kL z2 seenv z1 v Dz1 kd cd j1 HB HZ2 HZ1 Hkd Ez1 Hj1 Hsv0 Hsv R8 R9 R20.
pose proof HB as (HJ & HPM & Eab & HLEDL & HFR & R2 & R3 & R4).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
pose proof HJ as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (SpL : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB0.
pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b).
pose proof (rm_cell_low kd cd (Z.of_nat j1) Hkd ltac:(lia)) as (Z1a & Z1b). rewrite <- Ez1 in Z1a, Z1b.
destruct (gs_node_hdr _ _ _ _ _ HZ1) as (num1 & str1 & kids1 & keys1 & n1 & cap1 & Hh1).
destruct Hh1 as ((Hal8 & _) & (Hty0 & Hty) & _).
assert (KV : forall a n w, z1 <= a -> a + Z.of_nat n <= z1 + 56 ->
  val_mem SEGS (mrestrict (w_H W) mem) a n w -> val_mem SEGS (mrestrict (w_H WL) memL) a n w).
{ intros a n w H1 H2 Hv. apply (rm_val_lam lyL WL memL mdL kL kd cd a n w HJ Eab Hkd); [lia | lia | exact Hv]. }
set (E := rm_EL regsL regs [seenv; tag v]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q =
  ew (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; tag v])) q)
  by (intros q Hq; subst E; unfold rm_EL; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) =
  nth j0 (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; tag v])
    (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (EXS : forall j0, (j0 < 13)%nat -> ew E (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv)))).
{ intros j0 Hj0. change (33 + j0)%nat with (32 + Datatypes.S j0)%nat. rewrite EX by (unfold A_TEXT; lia).
  cbn [nth]. rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr regs (snd (0, 0%bv)))) by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun sr => getr regs (snd sr))). reflexivity. }
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regsL) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (U2' : bv_unsigned (ew E 2) = spZ regs - 128) by lia.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E47 : ew E 47 = Z_to_bv 64 (tag v)) by (change 47%nat with (32 + 15)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 z1) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (U9 : bv_unsigned (ew E 9) = z1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E243 : bv_unsigned (ew E 243) = VAL (A_OBJ 2)) by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_pentry
  (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 240))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pentry. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [subst E; unfold rm_EL; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite R20. symmetry. rewrite (gs_denot_off E 32 SHADOW_OFF 0 E32), Z.add_0_r. reflexivity.
  - vm_compute. reflexivity.
  - unfold rm_frame, rm_pnode. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]; rewrite ?U2, ?U9.
    + split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRS; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
        [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
            let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
          rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r;
          rewrite ?unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
          first [ exact Hsv0 | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
        | cbn; lia
        | change (N.to_nat 8) with 8%nat; rewrite SpL;
          first [ replace (spZ regs - 128 + 16) with (spZ regs - 112) by lia; exact Hsv
                | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                    apply (HFR (off, r)); cbn [rm_saves In]; tauto end ] ].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ z1 0 4 (SOff 47 0) (tag v));
        [rewrite (gs_denot_off E 47 (tag v) 0 E47), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply KV; [lia | cbn; lia | exact Hty].
  - apply pairwise_disjoint_of_extents. unfold rm_frame, rm_pnode, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [rm_sfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS RM_Bx RM_SHN E (mrestrict (w_H WL) memL))
  by exact (rm_shok_node E lyL WL memL mdL kL z1 kd cd j1 HJ Eab Hkd Ez1 Hj1 E32 E9).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
assert (AG0 : env_agree 64 E E) by apply env_agree_refl.
unfold rm_goal.
(* the shadow of params' type word, the word, the test against JArr's tag *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
pose proof HJ as (HARx & _).
rm_led_keep HFr U2 HARL HLEDL HLED1. clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK RM_span.
- (* not an array: the tail *)
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM RM_span (AF_rm + 456); [gs_awr regsL U2|].
  rm_led_keep HFr U2 HARx HLED1 HLED2. clear HF HG HFr.
  rm_frame_at HS U2' EXS HFR1 Hsv1.
  pmkst HS. replace (BASE + 4576) with (BASE + (AF_rm + 456)) by (rewrite EAF; reflexivity).
  lazymatch type of Hsv1 with val_mem _ _ _ _ ?sv => apply (rm_tail lyL WL (ms_regs ms0) (ms_mem ms0) _ kL z2 sv) end.
  + split; [exact HJ|]. split; [exact HPM|]. split; [exact Eab|]. split; [exact HLED2|]. split; [exact HFR1|].
    split; [rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
    split; [rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
    rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + exact HZ2.
  + unfold U. apply bv_unsigned_in_range.
  + exact Hsv1.
  + rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
- (* an array: the loop's set-up, then the params loop at item 0 *)
  rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  gs_tag_in Hc v E47. rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
  destruct (rm_tag5 v Hc) as (items & ->).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM RM_span (AF_rm + 328); [gs_awr regsL U2|].
  rm_led_keep HFr U2 HARx HLED1 HLED2. clear HF HG HFr.
  rm_frame_at HS U2' EXS HFR1 Hsv1.
  pmkst HS. replace (BASE + 4448) with (BASE + (AF_rm + 328)) by (rewrite EAF; reflexivity).
  eapply (rm_ploop (length items - 0)%nat 0%nat lyL WL (ms_regs ms0) (ms_mem ms0) _ kL z2 _ z1 items Dz1 kd cd j1 eq_refl
    ltac:(lia)).
  all: try (exact HZ2 || exact HZ1 || exact Hkd || exact Ez1 || exact Hj1 || exact Hsv1).
  + split; [exact HJ|]. split; [exact HPM|]. split; [exact Eab|]. split; [exact HLED2|]. split; [exact HFR1|].
    split; [rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
    split; [rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
    rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + unfold U. apply bv_unsigned_in_range.
  + rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG0; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG0. rewrite (gs_denot_off E 9 z1 24 E9). reflexivity.
  + rm_lreg HS AG0. rewrite (gs_denot_off E 9 z1 40 E9). reflexivity.
  + rm_lreg HS AG0. rewrite (gs_denot_off E 243 (VAL (A_OBJ 2)) 69952); [reflexivity|].
    rewrite <- E243. symmetry. apply Z_to_bv_bv_unsigned.
  + rm_lreg HS AG0. rewrite (gs_denot_off E 243 (VAL (A_OBJ 2)) 69984); [reflexivity|].
    rewrite <- E243. symmetry. apply Z_to_bv_bv_unsigned.
  + rm_lreg HS AG0. symmetry. eapply (rm_reg_sh2 E 32 9 SHADOW_OFF z1 0); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia
      | lia | unfold SHADOW_OFF; lia | unfold w64; rewrite Z.add_0_r; reflexivity].
  + rm_lreg HS AG0. reflexivity.
  + rm_lreg HS AG0. reflexivity.
  + rm_lreg HS AG0. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity.
  + rm_lreg HS AG0. symmetry. eapply (rm_reg_sh2 E 32 9 SHADOW_OFF z1 40); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia
      | lia | unfold SHADOW_OFF; lia | reflexivity].
  + rm_lreg HS AG0. symmetry. eapply (rm_reg_sh2 E 32 9 SHADOW_OFF z1 24); [exact E32 | exact E9 | unfold SHADOW_OFF; lia | lia
      | lia | unfold SHADOW_OFF; lia | reflexivity].
Qed.



(* ---- after the six keys (AF_rm + 192 ..): pj_get (doc, "plugin") and pj_get_str (its member, "id"), then the NULL
   test of params: NULL goes to the tail, a node to its type check ---- *)
Lemma rm_mid : forall lyL WL regsL memL mdL kL z1 z2 seenv,
  rm_base lyL WL regsL memL mdL kL -> rm_res z1 -> rm_res z2 ->
  0 <= seenv < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 112) 8 seenv ->
  getr regsL 8 = w64 z2 -> getr regsL 9 = w64 z1 -> getr regsL 18 = w64 doc -> getr regsL 20 = w64 SHADOW_OFF ->
  rm_goal WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 192))) memL (seg_rom SEGS)) mdL).
Proof.
intros lyL WL regsL memL mdL kL z1 z2 seenv HB HZ1 HZ2 Hsv0 Hsv R8 R9 R18 R20.
pose proof HB as (HJ & HPM & Eab & HLEDL & HFR & R2 & R3 & R4).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
pose proof HJ as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (SpL : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB0.
pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b). pose proof (rm_res_low z1 HZ1) as (Z1a & Z1b).
pose proof Hrs as (Hd4096 & _ & Hdamr & _).
assert (Hd47 : doc + 56 <= 2 ^ 47) by (unfold amem_range in Hdamr; rewrite C3, C4, C5 in Hdamr; lia).
set (E := rm_EL regsL regs [seenv]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q =
  ew (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv])) q)
  by (intros q Hq; subst E; unfold rm_EL; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) =
  nth j0 (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv]) (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (EXS : forall j0, (j0 < 13)%nat -> ew E (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv)))).
{ intros j0 Hj0. change (33 + j0)%nat with (32 + Datatypes.S j0)%nat. rewrite EX by (unfold A_TEXT; lia).
  cbn [nth]. rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr regs (snd (0, 0%bv)))) by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun sr => getr regs (snd sr))). reflexivity. }
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regsL) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (U2' : bv_unsigned (ew E 2) = spZ regs - 128) by lia.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_mid
  (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 192))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_mid. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [subst E; unfold rm_EL; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite R20. symmetry. rewrite (gs_denot_off E 32 SHADOW_OFF 0 E32), Z.add_0_r. reflexivity.
  - vm_compute. reflexivity.
  - unfold rm_frame. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]. rewrite U2.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HPRS; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
      [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
          let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
        rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r;
        rewrite ?unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
        first [ exact Hsv0 | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
      | cbn; lia
      | change (N.to_nat 8) with 8%nat; rewrite SpL;
        first [ replace (spZ regs - 128 + 16) with (spZ regs - 112) by lia; exact Hsv
              | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                  apply (HFR (off, r)); cbn [rm_saves In]; tauto end ] ].
  - apply pairwise_disjoint_of_extents. unfold rm_frame, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [rm_sfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS RM_Bx [] E (mrestrict (w_H WL) memL)) by constructor.
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
assert (AG0 : env_agree 64 E E) by apply env_agree_refl.
unfold rm_goal.
(* ---- C4: pj_get (doc, "plugin") at AF_rm + 204, returning to AF_rm + 208 ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
pose proof HJ as (HAR4 & _).
rm_led_keep HFr U2 HARL HLEDL HLED3. clear HF HG HFr.
prreg HS (1%bv : bv 5) Q14. rm_creg HS (2%bv : bv 5) Q24. rm_creg HS (3%bv : bv 5) Q34.
rm_creg HS (4%bv : bv 5) Q44. rm_creg HS (8%bv : bv 5) Q84. rm_creg HS (10%bv : bv 5) Q104.
rm_creg HS (11%bv : bv 5) Q114.
try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q24 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q34 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q44 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG0) in Q84 by reflexivity).
assert (HspT4 : spZ (ms_regs ms) = spZ regs + -128)
  by (unfold spZ at 1; rewrite Q24; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U2; lia).
destruct (rm_root ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own lyL WL (ms_mem ms) _ _ (ms_regs ms)
  (STK_pj_get (PI := prh_img_A)) HPRE Hnode Hrs HLED HJ Eab HspT4 ltac:(lia) ltac:(lia)) as (HN4 & HR4).
pose proof (rm_rod ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ HROD) as HROD4.
assert (Hin4 : In (VAL (A_OBJ 2) + 69920, 6) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
destruct (rm_key lyL S Hp WL (ms_mem ms) _ _ _ HAR4 HROD4 Hin4) as (lk4 & Hlk4 & HK4).
assert (HTOP4 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyL).
{ destruct (rm_ly ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ) as (_ & _ & Ghi). rewrite Ghi. lia. }
assert (HRAZ4 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 208)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite Q14, unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs WL E _ ms STKrm (spZ regs) []
    ly S Hp W mem md [] lyL S Hp _ _ (STK_pj_get (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ).
  - exact HspT4.
  - reflexivity.
  - lia.
  - exact FS4.
  - lia.
  - rewrite Q34. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv) by (lia || reflexivity).
    rewrite R3. exact Hgp.
  - rewrite Q44. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv) by (lia || reflexivity).
    rewrite R4. exact Htp.
  - exact Q14.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply rm_achain_low. unfold s0Z. rewrite Q84. cbn [sv_denot].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity).
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE4.
    refine (PJ_GET lyL S Hp WL (ms_regs ms) (ms_mem ms) _ [] (doc) (VAL (A_OBJ 2) + 69920) lk4
      _ _ Lam peak cnt fail ran most own (conj HPRE4 (conj HROD4 (conj HTOP4 (conj HRAZ4 HFRM)))) _ _ (or_intror (conj HN4 HR4))
      HK4 HLED3).
    + rewrite Q104. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 18%nat 18%bv), R18 by (lia || reflexivity). reflexivity.
    + rewrite Q114. rewrite (gs_denot_off _ 243 (VAL (A_OBJ 2)) 69920); [reflexivity|].
      rewrite <- (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). symmetry. apply Z_to_bv_bv_unsigned.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c4 Hwle4 (ly2 & S4 & Hp4 & regs4 & mem2 & md4 & kk4 & -> & HJ4 & HJc4 & HP4 & HQ4).
destruct HQ4 as ((EHp4 & ES4 & Eab4 & HLED4 & HROOM4 & HRES4) & HKP4).
subst Hp4 S4. rewrite Eab in Eab4.
assert (HPMn : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by (intros h; exact (HKP4 (HPM h))).
clear HPM HKP4. rename HPMn into HPM.
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W2) mem2) HP4 [0]%nat HSn.
lazymatch type of HSn with ?T -> _ => assert (HRK : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E);
    [exact HJc4 | exact HJ4 | try (rewrite (proj1 AG0 2%nat) by lia); exact U2 | lia | lia | lia | lia | lia]. }
specialize (HSn HRK). clear HRK HS. rename HSn into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E 64 (map (getr regs4) CLOB) HEI ltac:(cbv; lia)) as HEIn.
remember (havoc E 64 (map (getr regs4) CLOB)) as E1 eqn:HE4 in HS, HEIn.
assert (AG1 : env_agree 64 E E1) by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact AG0]).
assert (U2a : bv_unsigned (ew E1 2) = spZ regsL) by (rewrite (proj1 AG1 2%nat) by lia; exact U2).
assert (SHOKn : sh_ok SEGS RM_Bx [] E1 (mrestrict (w_H W2) mem2)) by constructor.
clear SHOK HEI. rename SHOKn into SHOK. rename HEIn into HEI.
(* C4's member: doc is no NULL, so its result word is a member of the document (rm_res) *)
destruct HRES4 as [(Hd0 & _) | (_ & HN4' & z4 & Ez4 & Hres4)]; [lia|].
pose proof (rm_res_of_get ly2 W2 mem2 md4 _ _ z4 HJ4 Eab4 HN4' Hres4) as HZ4.
pose proof (rm_res_low z4 HZ4) as (Z4a & Z4b).
assert (E1a0 : ew E1 68 = w64 z4) by (rewrite HE4, <- Ez4; reflexivity).
(* ---- C5: pj_get_str (z4, "id") at AF_rm + 216, returning to AF_rm + 220 ---- *)
pose proof HJ4 as (HAR5 & _).
paj_run_tok_x_inv RUN HS HJ4 SHOK HPM RM_span; [gs_awr regsL U2a|].
rm_led_keep HFr U2a HAR5 HLED4 HLED4k. clear HF HG HFr.
pose proof HJ4 as (HAR5k & _).
prreg HS (1%bv : bv 5) Q15. rm_creg HS (2%bv : bv 5) Q25. rm_creg HS (3%bv : bv 5) Q35.
rm_creg HS (4%bv : bv 5) Q45. rm_creg HS (8%bv : bv 5) Q85. rm_creg HS (10%bv : bv 5) Q105.
rm_creg HS (11%bv : bv 5) Q115.
try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q25 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q35 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q45 by reflexivity).
try (rewrite (sv_denot_agree 64 _ _ _ AG1) in Q85 by reflexivity).
assert (HspT5 : spZ (ms_regs ms0) = spZ regs + -128)
  by (unfold spZ at 1; rewrite Q25; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U2; lia).
assert (HO5 : exists v Dz, z4 = 0 \/ pj_nodeR SEGS (mrestrict (w_H W2) (ms_mem ms0)) (prh_lin Lam) z4 v Dz /\
    prhPj_rslot (PA := PA) B (STK_pj_get_str (PI := prh_img_A)) ly2 S W2 (ms_regs ms0) (ms_mem ms0) z4).
{ destruct (rm_res_at z4 ly2 W2 (ms_mem ms0) _ _ (ms_regs ms0) (STK_pj_get_str (PI := prh_img_A)) HZ4 HJ4 Eab4 ltac:(lia))
    as [Ez | (v & Dz & HN & HR)]; [exists t, D; left; exact Ez | exists v, Dz; right; split; assumption]. }
destruct HO5 as (vo5 & Do5 & HO5).
pose proof (rm_rod ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ4 HROD) as HROD5.
assert (Hin5 : In (VAL (A_OBJ 2) + 69696, 2) (rm_keys (PA := PA))) by (unfold rm_keys; cbn [map In]; tauto).
destruct (rm_key ly2 S Hp W2 (ms_mem ms0) _ _ _ HAR5k HROD5 Hin5) as (lk5 & Hlk5 & HK5).
assert (HTOP5 : spZ (ms_regs ms0) + 64 <= ly_stk_hi ly2).
{ destruct (rm_ly ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ4) as (_ & _ & Ghi). rewrite Ghi. lia. }
assert (HRAZ5 : raZ (ms_regs ms0) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 220)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite Q15, unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W2 E1 _ ms0 STKrm (spZ regs) []
    ly S Hp W mem md [] ly2 S Hp _ _ (STK_pj_get_str (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ4).
  - exact HspT5.
  - reflexivity.
  - lia.
  - exact FS5.
  - lia.
  - rewrite Q35. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv) by (lia || reflexivity).
    rewrite R3. exact Hgp.
  - rewrite Q45. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv) by (lia || reflexivity).
    rewrite R4. exact Htp.
  - exact Q15.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply rm_achain_low. unfold s0Z. rewrite Q85. cbn [sv_denot].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity).
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE5.
    refine (PJ_GET_STR ly2 S Hp W2 (ms_regs ms0) (ms_mem ms0) _ [] (z4) (VAL (A_OBJ 2) + 69696) lk5
      _ _ Lam peak cnt fail ran most own (conj HPRE5 (conj HROD5 (conj HTOP5 (conj HRAZ5 HFRM)))) _ _ HO5
      HK5 HLED4k).
    + rewrite Q105. cbn [sv_denot]. rewrite Z.add_0_r, E1a0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + rewrite Q115. rewrite (gs_denot_off _ 243 (VAL (A_OBJ 2)) 69696); [reflexivity|].
      rewrite <- (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). symmetry. apply Z_to_bv_bv_unsigned.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c5 Hwle5 (ly3 & S5 & Hp5 & regs5 & mem3 & md5 & kk5 & -> & HJ5 & HJc5 & HP5 & HQ5).
destruct HQ5 as ((EHp5 & ES5 & Eab5 & HLED5 & HROOM5 & HRES5) & HKP5).
subst Hp5 S5. rewrite Eab4 in Eab5.
assert (HPMn : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3) by (intros h; exact (HKP5 (HPM h))).
clear HPM HKP5. rename HPMn into HPM.
jafter_call_keep_pi HS 80%nat regs5 (mrestrict (w_H W3) mem3) HP5 [0]%nat HSn.
lazymatch type of HSn with ?T -> _ => assert (HRK : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E1);
    [exact HJc5 | exact HJ5 | try (rewrite (proj1 AG1 2%nat) by lia); exact U2 | lia | lia | lia | lia | lia]. }
specialize (HSn HRK). clear HRK HS. rename HSn into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E1 80 (map (getr regs5) CLOB) HEI ltac:(cbv; lia)) as HEIn.
remember (havoc E1 80 (map (getr regs5) CLOB)) as E2 eqn:HE5 in HS, HEIn.
assert (AG2 : env_agree 64 E E2) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact AG1]).
assert (U2b : bv_unsigned (ew E2 2) = spZ regsL) by (rewrite (proj1 AG2 2%nat) by lia; exact U2).
assert (SHOKn : sh_ok SEGS RM_Bx [] E2 (mrestrict (w_H W3) mem3)) by constructor.
clear SHOK HEI. rename SHOKn into SHOK. rename HEIn into HEI.
(* ---- the seen update and the NULL test of params (AF_rm + 236) ---- *)
pose proof HJ5 as (HAR6 & _).
paj_run_tok_x_inv RUN HS HJ5 SHOK HPM RM_span; [gs_awr regsL U2b|].
rm_led_keep HFr U2b HAR6 HLED5 HLED5k. clear HF HG HFr.
pose proof HJ5 as (HARy & _).
psrr_branch_tok RUN BR HS SHOK RM_span.
- (* params is NULL: the tail *)
  clear Hc. paj_run_to_tok_x_inv RUNTO HS HJ5 SHOK HPM RM_span (AF_rm + 456); [gs_awr regsL U2b|].
  rm_led_keep HFr U2b HARy HLED5k HLEDx. clear HF HG HFr.
  assert (U2B : bv_unsigned (ew E2 2) = spZ regs - 128) by (rewrite (proj1 AG2 2%nat) by lia; lia).
  assert (EXSB : forall j0, (j0 < 13)%nat -> ew E2 (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv))))
    by (intros j0 Hj0; rewrite (proj1 AG2 (33 + j0)%nat) by lia; apply EXS; exact Hj0).
  rm_frame_at HS U2B EXSB HFR1 Hsv1.
  pmkst HS. replace (BASE + 4576) with (BASE + (AF_rm + 456)) by (rewrite EAF; reflexivity).
  rename HJ5 into HJx. rename Eab5 into Eabx.
  lazymatch type of Hsv1 with val_mem _ _ _ _ ?sv => eapply (rm_tail ly3 W3 (ms_regs ms2) (ms_mem ms2) _ _ z2 sv) end.
  + split; [exact HJx|]. split; [exact HPM|]. split; [exact Eabx|]. split; [exact HLEDx|]. split; [exact HFR1|].
  split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
  split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
  rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + exact HZ2.
  + unfold U. apply bv_unsigned_in_range.
  + exact Hsv1.
  + rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
- (* params is a node: its type check *)
  rewrite branch_eq_U, U_SLit in Hc. apply Z.eqb_neq in Hc.
  rewrite (U_atom E2 9 z1) in Hc
    by (try (rewrite (proj1 AG2 9%nat) by lia; rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact R9); lia).
  rewrite zcanon_id in Hc by (unfold M64; lia).
  destruct HZ1 as [Ez0 | (v1 & Dz1 & kd & cd & j1 & HN1 & Hk1 & Ez1 & Hj1)]; [lia|].
  paj_run_to_tok_x_inv RUNTO HS HJ5 SHOK HPM RM_span (AF_rm + 240); [gs_awr regsL U2b|].
  rm_led_keep HFr U2b HARy HLED5k HLEDx. clear HF HG HFr.
  assert (U2B : bv_unsigned (ew E2 2) = spZ regs - 128) by (rewrite (proj1 AG2 2%nat) by lia; lia).
  assert (EXSB : forall j0, (j0 < 13)%nat -> ew E2 (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv))))
    by (intros j0 Hj0; rewrite (proj1 AG2 (33 + j0)%nat) by lia; apply EXS; exact Hj0).
  rm_frame_at HS U2B EXSB HFR1 Hsv1.
  pmkst HS. replace (BASE + 4360) with (BASE + (AF_rm + 240)) by (rewrite EAF; reflexivity).
  rename HJ5 into HJx. rename Eab5 into Eabx.
  lazymatch type of Hsv1 with val_mem _ _ _ _ ?sv =>
    eapply (rm_pentry ly3 W3 (ms_regs ms2) (ms_mem ms2) _ _ z2 sv z1 v1 Dz1 kd cd j1) end.
  + split; [exact HJx|]. split; [exact HPM|]. split; [exact Eabx|]. split; [exact HLEDx|]. split; [exact HFR1|].
  split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
  split; [rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
  rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + exact HZ2.
  + exact HN1.
  + exact Hk1.
  + exact Ez1.
  + exact Hj1.
  + unfold U. apply bv_unsigned_in_range.
  + exact Hsv1.
  + rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG2; cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by (unfold SHADOW_OFF; lia); reflexivity.
Qed.




(* ---- the six keys of the table `top` (AF_rm + 140 ..): pj_get_str (doc, top[i]); by induction on the keys left; after
   the sixth, the segment after the loop ---- *)
Lemma rm_top_loop : forall (k i : nat) lyL WL regsL memL mdL kL z1 z2 seenv,
  (6 - i = k)%nat -> (i < 6)%nat ->
  rm_base lyL WL regsL memL mdL kL -> rm_res z1 -> rm_res z2 ->
  0 <= seenv < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H WL) memL) (spZ regs - 112) 8 seenv ->
  getr regsL 8 = w64 z2 -> getr regsL 9 = w64 z1 -> getr regsL 18 = w64 doc ->
  getr regsL 19 = w64 (- 8 * Z.of_nat i) -> getr regsL 20 = w64 SHADOW_OFF ->
  getr regsL 21 = w64 (VAL (A_OBJ 3) + 8 * Z.of_nat i) ->
  getr regsL 22 = w64 (SHADOW_OFF + (VAL (A_OBJ 3) + 8 * Z.of_nat i) / 8) -> getr regsL 23 = w64 (- 48) ->
  rm_goal WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 140))) memL (seg_rom SEGS)) mdL).
Proof.
intros k. induction k as [k IH] using lt_wf_ind.
intros i lyL WL regsL memL mdL kL z1 z2 seenv Hk Hi HB HZ1 HZ2 Hsv0 Hsv R8 R9 R18 R19 R20 R21 R22 R23.
pose proof HB as (HJ & HPM & Eab & HLEDL & HFR & R2 & R3 & R4).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
pose proof HJ as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (SpL : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB0.
pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b). pose proof (rm_res_low z1 HZ1) as (Z1a & Z1b).
pose proof Hrs as (Hd4096 & _ & Hdamr & _).
assert (Hd47 : doc + 56 <= 2 ^ 47) by (unfold amem_range in Hdamr; rewrite C3, C4, C5 in Hdamr; lia).
(* the table and the i-th key *)
pose proof RM_IMG as (RI & (TLO & THI & _) & _).
rewrite PAB in TLO. rewrite PAH in THI. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in TLO, THI.
set (kp := nth i (rm_keys (PA := PA)) (0, 0)).
assert (Hkin : In (fst kp, snd kp) (rm_keys (PA := PA))).
{ rewrite <- surjective_pairing. subst kp. apply nth_In. unfold rm_keys. rewrite length_map. cbn. lia. }
destruct (RI _ _ Hkin) as ((KLO & KHI & _) & _).
rewrite PAB in KLO. rewrite PAH in KHI. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in KLO, KHI.
assert (Hkn : 0 <= snd kp).
{ subst kp. clear - Hi. unfold rm_keys.
  do 6 (destruct i as [|i]; [cbn; lia|]). lia. }
pose proof (rm_rod ly S Hp W mem md lyL S Hp WL memL mdL kL (spZ regs) HJ HROD) as HRODL.
destruct (rm_top lyL S Hp WL memL mdL i HARL HRODL Hi) as (Htv & Htra).
fold kp in Htv.
set (E := rm_EL regsL regs [seenv; fst kp]).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q =
  ew (Ereg regsL (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; fst kp])) q)
  by (intros q Hq; subst E; unfold rm_EL; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) =
  nth j0 (Z_to_bv 64 SHADOW_OFF :: map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seenv; fst kp])
    (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (EXS : forall j0, (j0 < 13)%nat -> ew E (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv)))).
{ intros j0 Hj0. change (33 + j0)%nat with (32 + Datatypes.S j0)%nat. rewrite EX by (unfold A_TEXT; lia).
  cbn [nth]. rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr regs (snd (0, 0%bv)))) by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun sr => getr regs (snd sr))). reflexivity. }
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regsL) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (U2' : bv_unsigned (ew E 2) = spZ regs - 128) by lia.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E47 : ew E 47 = Z_to_bv 64 (fst kp)) by (change 47%nat with (32 + 15)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 (VAL (A_OBJ 3) + 8 * Z.of_nat i)) by (rewrite (ER 21%nat 21%bv) by (lia || reflexivity); exact R21).
assert (U21 : bv_unsigned (ew E 21) = VAL (A_OBJ 3) + 8 * Z.of_nat i) by (rewrite E21; apply unsigned_lit_small; lia).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_top
  (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + (AF_rm + 140))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_top. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_pin; [subst E; unfold rm_EL; apply regs_ok_Eimg_Ereg | |] | |];
      try (intros X; discriminate X).
    + rewrite R22. eapply (rm_reg_sh E 32 21 SHADOW_OFF (VAL (A_OBJ 3) + 8 * Z.of_nat i) 0); [exact E32 | exact E21
        | unfold SHADOW_OFF; lia | lia | lia | unfold SHADOW_OFF; lia | unfold w64; rewrite Z.add_0_r; reflexivity].
    + rewrite R23. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold rm_frame, rm_tcell. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]; rewrite ?U2, ?U21.
    + split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRS; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
        [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
            let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
          rewrite EX by (unfold A_TEXT; lia); cbn [nth map app rm_saves snd]; rewrite Z.add_0_r;
          rewrite ?unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
          first [ exact Hsv0 | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
        | cbn; lia
        | change (N.to_nat 8) with 8%nat; rewrite SpL;
          first [ replace (spZ regs - 128 + 16) with (spZ regs - 112) by lia; exact Hsv
                | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                    apply (HFR (off, r)); cbn [rm_saves In]; tauto end ] ].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 3) + 8 * Z.of_nat i) 0 8 (SOff 47 0) (fst kp));
        [rewrite (gs_denot_off E 47 (fst kp) 0 E47), Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia |].
      rewrite Z.add_0_r. exact Htv.
  - apply pairwise_disjoint_of_extents. unfold rm_frame, rm_tcell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [rm_sfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U21, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold IMG_LO, IMG_TOP.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok SEGS RM_Bx RM_SHT E (mrestrict (w_H WL) memL)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H WL) memL E RM_Bx 21 (VAL (A_OBJ 3) + 8 * Z.of_nat i) 8
    (VAL (A_OBJ 3) + 8 * Z.of_nat i) 0 8 Htra).
  - unfold RM_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
  - apply (U_atom E 21 _ E21). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
assert (AG0 : env_agree 64 E E) by apply env_agree_refl.
unfold rm_goal.
(* ---- C3: pj_get_str (doc, top[i]) at AF_rm + 156, returning to AF_rm + 160 ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regsL U2|].
pose proof HJ as (HAR3 & _).
rm_led_keep HFr U2 HARL HLEDL HLED3. clear HF HG HFr.
prreg HS (1%bv : bv 5) Q13. rm_creg HS (2%bv : bv 5) Q23. rm_creg HS (3%bv : bv 5) Q33.
rm_creg HS (4%bv : bv 5) Q43. rm_creg HS (8%bv : bv 5) Q83. rm_creg HS (10%bv : bv 5) Q103.
rm_creg HS (11%bv : bv 5) Q113.
assert (HspT3 : spZ (ms_regs ms) = spZ regs + -128)
  by (unfold spZ at 1; rewrite Q23; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U2; lia).
destruct (rm_root ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own lyL WL (ms_mem ms) _ _ (ms_regs ms)
  (STK_pj_get_str (PI := prh_img_A)) HPRE Hnode Hrs HLED HJ Eab HspT3 ltac:(lia) ltac:(lia)) as (HN3 & HR3).
pose proof (rm_rod ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ HROD) as HROD3.
destruct (rm_key lyL S Hp WL (ms_mem ms) _ _ _ HAR3 HROD3 Hkin) as (lk3 & Hlk3 & HK3).
assert (HTOP3 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyL).
{ destruct (rm_ly ly S Hp W mem md lyL S Hp WL (ms_mem ms) _ _ (spZ regs) HJ) as (_ & _ & Ghi). rewrite Ghi. lia. }
assert (HRAZ3 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 160)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite Q13, unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs WL E _ ms STKrm (spZ regs) []
    ly S Hp W mem md [] lyL S Hp _ _ (STK_pj_get_str (PI := prh_img_A)) [] (-128) _ [] _ HS eq_refl HJ).
  - exact HspT3.
  - reflexivity.
  - lia.
  - exact FS5.
  - lia.
  - rewrite Q33. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv) by (lia || reflexivity).
    rewrite R3. exact Hgp.
  - rewrite Q43. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv) by (lia || reflexivity).
    rewrite R4. exact Htp.
  - exact Q13.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply rm_achain_low. unfold s0Z. rewrite Q83. cbn [sv_denot].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity).
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE3.
    refine (PJ_GET_STR lyL S Hp WL (ms_regs ms) (ms_mem ms) _ [] doc (fst kp) lk3 t D Lam peak cnt fail ran most own
      (conj HPRE3 (conj HROD3 (conj HTOP3 (conj HRAZ3 HFRM)))) _ _ (or_intror (conj HN3 HR3)) HK3 HLED3).
    + rewrite Q103. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 18%nat 18%bv), R18 by (lia || reflexivity).
      reflexivity.
    + rewrite Q113. cbn [sv_denot]. rewrite Z.add_0_r, E47. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c3 Hwle3 (ly2 & S3 & Hp3 & regs3 & mem2 & md3 & kk3 & -> & HJ3 & HJc3 & HP3 & HQ3).
destruct HQ3 as ((EHp3 & ES3 & Eab3 & HLED4 & HROOM3 & HRES3) & HKP3).
subst Hp3 S3. rewrite Eab in Eab3.
assert (HPMn : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by (intros h; exact (HKP3 (HPM h))).
clear HPM HKP3. rename HPMn into HPM.
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem2) HP3 [0]%nat HSn.
lazymatch type of HSn with ?T -> _ => assert (HRK : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E);
    [exact HJc3 | exact HJ3 | exact U2 | lia | lia | lia | lia | lia]. }
specialize (HSn HRK). clear HRK HS. rename HSn into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E 64 (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEIn.
remember (havoc E 64 (map (getr regs3) CLOB)) as E1 eqn:HE3 in HS, HEIn.
assert (AG1 : env_agree 64 E E1) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact AG0]).
assert (U2a : bv_unsigned (ew E1 2) = spZ regsL) by (rewrite (proj1 AG1 2%nat) by lia; exact U2).
assert (SHOKn : sh_ok SEGS RM_Bx [] E1 (mrestrict (w_H W2) mem2)) by constructor.
clear SHOK HEI. rename SHOKn into SHOK. rename HEIn into HEI.
(* the seen update, i := i + 1, the loop test *)
pose proof HJ3 as (HAR4 & _).
paj_run_tok_x_inv RUN HS HJ3 SHOK HPM RM_span; [gs_awr regsL U2a|].
rm_led_keep HFr U2a HAR4 HLED4 HLED5. clear HF HG HFr.
pose proof HJ3 as (HAR5 & _).
assert (U2B : bv_unsigned (ew E1 2) = spZ regs - 128) by (rewrite (proj1 AG1 2%nat) by lia; lia).
assert (EXSB : forall j0, (j0 < 13)%nat -> ew E1 (33 + j0) = getr regs (snd (nth j0 rm_saves (0, 0%bv))))
  by (intros j0 Hj0; rewrite (proj1 AG1 (33 + j0)%nat) by lia; apply EXS; exact Hj0).
psrr_branch_tok RUN BR HS SHOK RM_span.
- (* taken: the next key *)
  rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hne.
  assert (Hi5 : i <> 5%nat).
  { intros ->. apply Hne. rewrite U_SOff, (proj1 AG1 19%nat), (ER 19%nat 19%bv), R19 by (lia || reflexivity).
    rewrite U_SLit. vm_compute. reflexivity. }
  paj_run_to_tok_x_inv RUNTO HS HJ3 SHOK HPM RM_span (AF_rm + 140); [gs_awr regsL U2a|].
  rm_led_keep HFr U2a HAR5 HLED5 HLED6. clear HF HG HFr.
  rm_frame_at HS U2B EXSB HFR1 Hsv1.
  pmkst HS. replace (BASE + 4260) with (BASE + (AF_rm + 140)) by (rewrite EAF; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdB) _ =>
    eapply (IH (6 - Datatypes.S i)%nat ltac:(lia) (Datatypes.S i) ly2 W2 (ms_regs ms1) (ms_mem ms1) mdB _ z1 z2 _ eq_refl
      ltac:(lia)) end.
  all: try (exact HZ1 || exact HZ2 || exact Hsv1).
  + split; [exact HJ3|]. split; [exact HPM|]. split; [exact Eab3|]. split; [exact HLED6|]. split; [exact HFR1|].
    split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
    split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
    rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + unfold U. apply bv_unsigned_in_range.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 18%nat 18%bv), R18 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1. cbn [sv_denot]. rewrite (ER 19%nat 19%bv), R19 by (lia || reflexivity). unfold w64.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 20%nat 20%bv), R20 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1. cbn [sv_denot]. rewrite U21. unfold w64. f_equal. lia.
  + rm_lreg HS AG1. rewrite (denot_lit_U E). unfold w64. f_equal.
    rewrite (U_SAlu E ALU_ADD _ (SLit 1)), U_SLit.
    rewrite (gs_U_shadow_of E 32 21 SHADOW_OFF (VAL (A_OBJ 3) + 8 * Z.of_nat i) E32 E21) by (unfold SHADOW_OFF; lia).
    cbn [zalu_raw]. rewrite (zcanon_id 1) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia).
    lia.
  + rm_lreg HS AG1. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity.
- (* not taken: the sixth key was the last; the segment after the loop *)
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ3 SHOK HPM RM_span (AF_rm + 192); [gs_awr regsL U2a|].
  rm_led_keep HFr U2a HAR5 HLED5 HLED6. clear HF HG HFr.
  rm_frame_at HS U2B EXSB HFR1 Hsv1.
  pmkst HS. replace (BASE + 4312) with (BASE + (AF_rm + 192)) by (rewrite EAF; reflexivity).
  lazymatch type of Hsv1 with val_mem _ _ _ _ ?sv =>
    eapply (rm_mid ly2 W2 (ms_regs ms1) (ms_mem ms1) _ _ z1 z2 sv) end.
  + split; [exact HJ3|]. split; [exact HPM|]. split; [exact Eab3|]. split; [exact HLED6|]. split; [exact HFR1|].
    split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 2%nat 2%bv), R2 by (lia || reflexivity); reflexivity|].
    split; [rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 3%nat 3%bv), R3 by (lia || reflexivity); reflexivity|].
    rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 4%nat 4%bv), R4 by (lia || reflexivity); reflexivity.
  + exact HZ1.
  + exact HZ2.
  + unfold U. apply bv_unsigned_in_range.
  + exact Hsv1.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 8%nat 8%bv), R8 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 9%nat 9%bv), R9 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 18%nat 18%bv), R18 by (lia || reflexivity); reflexivity.
  + rm_lreg HS AG1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER 20%nat 20%bv), R20 by (lia || reflexivity); reflexivity.
Qed.

(* ---- the walk from the entry: the prologue, pj_get (doc, "params") and (doc, "state"), up to the six-key loop ---- *)
Ltac rm_mreg HS r G := pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
  lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
    let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end.
Lemma rm_body : getr regs 10 = w64 doc ->
  rm_goal W (cfg_at SEGS (pa_sigma AS_read_members) regs mem md).
Proof.
intros H10. unfold rm_goal.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct rm_stk as (FS1 & FS2 & FS3 & Hes & FS4 & FS5).
destruct (rm_entry ly S Hp W regs mem md ch [] HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (rm_E regs []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_E; apply Eimg_env).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
assert (HPM : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_rm)) with (Z_to_bv 64 (BASE + AF_rm)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_span; [gs_awr regs Usp|].
(* ---- C1: pj_get (doc, "params"), at the entry offset AF_rm + 84, returning to AF_rm + 88 ---- *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (HspT : spZ (ms_regs ms) = spZ regs + -128)
  by (unfold spZ at 1; rewrite R2, Usp; rewrite unsigned_lit_small by lia; lia).
assert (Hs0 : s0Z (ms_regs ms) = s0Z regs)
  by (unfold s0Z at 1; rewrite R8; subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); reflexivity).
assert (E243 : bv_unsigned (ew E 243) = VAL (A_OBJ 2))
  by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8%bv)
  by (subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold rm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
(* the memory after the prologue: only the own frame changed *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply (gs_mr_keep E (ss_mem ss_rm) _ _ a HFr); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr|..]; lia. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite (KM a Ha Hn); reflexivity).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
assert (HLED1 : prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own HLED).
  - intros a Ha. apply KL. apply Exists_exists in Ha as (r & Hin & Hr). vm_compute in Hin. unfold in_zr in Hr.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - intros a k0 i Hin Hi. pose proof HW as HWv. unfold prh_head_wide in HWv.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k0 most own HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k0 + cf_head) HAR Hab) as (_ & H4096 & Hc & _).
    rewrite gs_req in Hc by lia. apply KL. clear -H4096 Hc Hi Hk0 HWv. lia.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) (ms_mem ms)))
  by exact (gs_rod_kept (PA := PA) B W W mem (ms_mem ms) HROD KL).
(* the key "params": the seventh literal of rm_keys *)
assert (Hin1 : In (VAL (A_OBJ 2) + 69856, 6) (rm_keys (PA := PA)))
  by (unfold rm_keys; cbn [map In]; tauto).
pose proof HJ as (HAR1 & _).
destruct (rm_key ly S Hp W (ms_mem ms) _ _ _ HAR1 HROD1 Hin1) as (l1 & Hl1len & HK1).
(* the document at the callee *)
destruct (rm_root ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own ly W (ms_mem ms) _ 0 (ms_regs ms)
  (STK_pj_get (PI := prh_img_A)) HPRE Hnode Hrs HLED HJ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as (HN1 & HR1).
assert (HTOP1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by lia.
lazymatch eval vm_compute in AF_rm with ?n => assert (EAF : AF_rm = n) by (vm_compute; reflexivity) end.
pose proof (@pa_B_ok _ _ PA) as HB.
assert (HRAZ1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 88)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite R1, unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W E _ ms STKrm (spZ regs) []
    ly S Hp W mem md [] ly S Hp _ 0 (STK_pj_get (PI := prh_img_A)) [] (-128) _ ch _ HS eq_refl HJ).
  - exact HspT.
  - reflexivity.
  - lia.
  - exact FS4.
  - lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0.
    exact (rm_achain ly S Hp W regs mem md ly S Hp W (ms_mem ms) _ 0 (spZ regs + -128) (s0Z regs) ch HJ Hstk Hch
      ltac:(lia)).
  - intros HPRE1.
    exact (PJ_GET ly S Hp W (ms_regs ms) (ms_mem ms) _ ch doc (VAL (A_OBJ 2) + 69856) l1 t D Lam peak cnt fail ran most own
      (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) ltac:(rewrite R10, E10; exact H10)
      ltac:(rewrite R11, E243; reflexivity) (or_intror (conj HN1 HR1)) HK1 HLED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk1 & -> & HJ2 & HJc & HP2 & HQ2).
destruct HQ2 as ((EHp1 & ES1 & Eab1 & HLED2 & HROOM1 & HRES1) & HKP1).
subst Hp2 S2.
(* C1's member params, as rm_res (doc is no NULL) *)
destruct HRES1 as [(Hd0 & _) | (_ & HN1' & z1 & Ez1 & Hres1)]; [pose proof Hrs as (Hd4096 & _); lia|].
pose proof (rm_res_of_get ly2 W2 mem2 md2 _ _ z1 HJ2 Eab1 HN1' Hres1) as HZ1.
assert (HPM2 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by (intros h; exact (HKP1 (HPM h))).
clear HPM HKP1. rename HPM2 into HPM.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?T -> _ => assert (HRK : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E);
    [exact HJc | exact HJ2 | exact Usp | lia | lia | lia | lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rename HS2 into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E 40 (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
remember (havoc E 40 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS, HEI2.
assert (OLD1 : forall q, (q < 40)%nat -> ew E1 q = ew E q) by (intros q Hq; rewrite HE1; apply ew_havoc_old; lia).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
assert (SHOK1 : sh_ok SEGS RM_Bx [] E1 (mrestrict (w_H W2) mem2)) by constructor.
clear SHOK HEI. rename HEI2 into HEI. rename SHOK1 into SHOK.
(* ---- the segment to C2: s1 = the result of C1, a1 = "state", a0 = doc ---- *)
paj_run_tok_x_inv RUN HS HJ2 SHOK HPM RM_span; [gs_awr regs Usp1|].
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (HspT2 : spZ (ms_regs ms0) = spZ regs + -128)
  by (unfold spZ at 1; rewrite Q2, Usp1; rewrite unsigned_lit_small by lia; lia).
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  mrestrict (w_H W2) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a)).
{ intros a Ha Hn. apply (gs_mr_keep E1 _ _ _ a HFr0); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp1 in Hr; lia. }
assert (KL2 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; unfold aview, mbyte; rewrite KM2 by lia; reflexivity).
pose proof HJ2 as (HAR2 & _).
assert (HLED3 : prh_ledger (PI := prh_img_A) (PA := PA) B ly2 S Hp W2 (ms_mem ms0) Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly2 S Hp W2 mem2 ly2 S Hp W2 (ms_mem ms0) Lam peak cnt fail ran most own HLED2).
  - intros a Ha. apply KL2. apply Exists_exists in Ha as (r & Hin & Hr). vm_compute in Hin. unfold in_zr in Hr.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - intros a k0 i Hin Hi. pose proof HW as HWv. unfold prh_head_wide in HWv.
    destruct (prh_ledger_hblock B ly2 S Hp W2 mem2 Lam peak cnt fail ran a k0 most own HLED2 Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S Hp W2 (ms_mem ms0) _ (a - cf_head) (k0 + cf_head) HAR2 Hab)
      as (_ & H4096 & Hc & _).
    rewrite gs_req in Hc by lia. apply KL2. clear -H4096 Hc Hi Hk0 HWv. lia.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
assert (HROD3 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) (ms_mem ms0)))
  by exact (rm_rod ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ2 HROD).
assert (Hin2 : In (VAL (A_OBJ 2) + 69888, 5) (rm_keys (PA := PA)))
  by (unfold rm_keys; cbn [map In]; tauto).
pose proof HJ2 as (HAR3 & _).
destruct (rm_key ly2 S Hp W2 (ms_mem ms0) _ _ _ HAR3 HROD3 Hin2) as (l2 & Hl2len & HK2).
destruct (rm_root ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own ly2 W2 (ms_mem ms0) _ _ (ms_regs ms0)
  (STK_pj_get (PI := prh_img_A)) HPRE Hnode Hrs HLED HJ2 Eab1 ltac:(lia) ltac:(lia) ltac:(lia)) as (HN2 & HR2).
assert (HTOP2 : spZ (ms_regs ms0) + 64 <= ly_stk_hi ly2).
{ destruct (rm_ly ly S Hp W mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs) HJ2) as (_ & _ & Ghi).
  rewrite Ghi. lia. }
assert (HRAZ2 : raZ (ms_regs ms0) < YM05.alloc_ceiling).
{ pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_rm + 108)
    ltac:(rewrite EAF; lia) ltac:(rewrite EAF; vm_compute; reflexivity)) as HSL.
  rewrite EAF in HSL. unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
assert (E1_243 : bv_unsigned (ew E1 243) = VAL (A_OBJ 2))
  by exact (HEI (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W2 E1 _ ms0 STKrm (spZ regs) []
    ly S Hp W mem md [] ly2 S Hp _ _ (STK_pj_get (PI := prh_img_A)) [] (-128) _ ch _ HS eq_refl HJ2).
  - exact HspT2.
  - reflexivity.
  - lia.
  - exact FS4.
  - lia.
  - rewrite Q3, OLD1 by lia. rewrite E3. exact Hgp.
  - rewrite Q4, OLD1 by lia. rewrite E4. exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Q8, OLD1 by lia. rewrite E8. fold (s0Z regs).
    exact (rm_achain ly S Hp W regs mem md ly2 S Hp W2 (ms_mem ms0) _ _ (spZ regs + -128) (s0Z regs) ch HJ2 Hstk Hch
      ltac:(lia)).
  - intros HPRE2.
    exact (PJ_GET ly2 S Hp W2 (ms_regs ms0) (ms_mem ms0) _ ch doc (VAL (A_OBJ 2) + 69888) l2 t D Lam peak cnt fail ran most own
      (conj HPRE2 (conj HROD3 (conj HTOP2 (conj HRAZ2 HFRM)))) ltac:(rewrite Q10, OLD1 by lia; rewrite E10; exact H10)
      ltac:(rewrite Q11, E1_243; reflexivity) (or_intror (conj HN2 HR2)) HK2 HLED3).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & kk2 & -> & HJ3 & HJc3 & HP3 & HQ3).
destruct HQ3 as ((EHp2 & ES2 & Eab2 & HLED4 & HROOM2 & HRES2) & HKP2).
subst Hp3 S3. rewrite Eab1 in Eab2.
(* C2's member state, as rm_res *)
destruct HRES2 as [(Hd0 & _) | (_ & HN2' & z2 & Ez2 & Hres2)]; [pose proof Hrs as (Hd4096 & _); lia|].
pose proof (rm_res_of_get ly3 W3 mem3 md3 _ _ z2 HJ3 Eab2 HN2' Hres2) as HZ2.
assert (HPM3 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3) by (intros h; exact (HKP2 (HPM h))).
clear HPM HKP2. rename HPM3 into HPM.
jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
lazymatch type of HS3 with ?T -> _ => assert (HRK3 : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARx E1);
    [exact HJc3 | exact HJ3 | exact Usp1 | lia | lia | lia | lia | lia]. }
specialize (HS3 HRK3). clear HRK3 HS. rename HS3 into HS.
rewrite <- restrict_mkst_fx in HS.
pose proof (img_env_havoc (PI := PA) E1 56 (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
remember (havoc E1 56 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS, HEI3.
assert (OLD2 : forall q, (q < 56)%nat -> ew E2 q = ew E1 q) by (intros q Hq; rewrite HE2; apply ew_havoc_old; lia).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp1).
assert (SHOK2 : sh_ok SEGS RM_Bx [] E2 (mrestrict (w_H W3) mem3)) by constructor.
clear SHOK HEI. rename HEI3 into HEI. rename SHOK2 into SHOK.
(* ---- the segment to the head of the top loop (AF_rm + 140): s0 = C2's result, seen := 0, s5 = top,
       s6 = the shadow byte of top, s7 = -48, s3 = 0 ---- *)
pose proof HJ3 as (HARm & _).
paj_run_to_tok_x_inv RUNTO HS HJ3 SHOK HPM RM_span (AF_rm + 140); [gs_awr regs Usp2|].
(* ---- the head of the six-key loop: the loop's facts at key 0, then rm_top_loop ---- *)
gs_keep HFr1 Usp2 (spZ regs - 128) (spZ regs) K9. clear HF1 HG1 HFr1.
assert (KL9 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha; apply K9; lia).
pose proof (rm_ledger_keep ly3 W3 mem3 (ms_mem ms1) _ HARm HLED4 KL9) as HLED9.
assert (EE : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E2 q = getr regs r).
{ intros q r Hq Hr. rewrite OLD2, OLD1 by lia. subst E. unfold rm_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ q r Hr). }
assert (E2_32 : ew E2 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite OLD2, OLD1 by lia. subst E. unfold rm_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (E2_244 : ew E2 244 = Z_to_bv 64 (VAL (A_OBJ 3))).
{ rewrite <- (HEI (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). symmetry. apply Z_to_bv_bv_unsigned. }
pose proof (st_ok_region_nth SEGS _ _ _ 0 _ HS eq_refl) as RG9. cbn [ms_mem restrict] in RG9.
assert (HFR9 : Forall (fun sr => val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (spZ regs - 128 + fst sr) 8
    (bv_unsigned (getr regs (snd sr)))) rm_saves).
{ apply Forall_forall. intros sr Hsr. cbn [rm_saves In] in Hsr.
  repeat (destruct Hsr as [<- | Hsr];
    [ cbn [fst snd]; lazymatch goal with |- val_mem _ _ (_ - 128 + ?od) _ (bv_unsigned (getr regs ?r)) =>
        let q := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
        replace (spZ regs - 128 + od) with (spZ regs + (od - 128)) by lia;
        eapply (slot_of_region SEGS E2 _ _ _ _ _ _ _ _ (SOff q 0) _ RG9 Usp2);
        [ cbn [In]; repeat first [left; reflexivity | right]
        | rewrite (gs_denot_off E2 q (bv_unsigned (getr regs r)) 0);
          [ rewrite Z.add_0_r; reflexivity
          | rewrite (EE q r) by (lia || reflexivity); symmetry; apply Z_to_bv_bv_unsigned ]
        | apply bv_unsigned_in_range ] end |]).
  destruct Hsr. }
assert (Hsv9 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (spZ regs - 112) 8 0).
{ replace (spZ regs - 112) with (spZ regs + -112) by lia.
  eapply (slot_of_region SEGS E2 _ _ _ _ _ _ _ _ (SLit 0) _ RG9 Usp2);
    [ cbn [In]; repeat first [left; reflexivity | right] | reflexivity | lia ]. }
pose proof (rm_res_low z1 HZ1) as (Z1a & Z1b). pose proof (rm_res_low z2 HZ2) as (Z2a & Z2b).
pose proof (pa_val_range (PAImg := PA) (A_OBJ 3)) as Rtop.
pose proof RM_IMG as (_ & (TLO & THI & _) & _).
rewrite PAB in TLO. rewrite PAH in THI. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in TLO, THI.
pmkst HS. replace (BASE + 4260) with (BASE + (AF_rm + 140)) by (rewrite EAF; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdB) _ =>
  eapply (rm_top_loop 6 0 ly3 W3 (ms_regs ms1) (ms_mem ms1) mdB _ z1 z2 0 eq_refl ltac:(lia)) end.
- split; [exact HJ3|]. split; [exact HPM|]. split; [exact Eab2|]. split; [exact HLED9|]. split; [exact HFR9|].
  split; [rm_mreg HS (2%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Usp2; reflexivity|].
  split; [rm_mreg HS (3%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    apply (EE 3%nat 3%bv); lia || reflexivity|].
  rm_mreg HS (4%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    apply (EE 4%nat 4%bv); lia || reflexivity.
- exact HZ1.
- exact HZ2.
- lia.
- exact Hsv9.
- rm_mreg HS (8%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite HE2. exact Ez2.
- rm_mreg HS (9%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite OLD2 by lia. rewrite HE1. exact Ez1.
- rm_mreg HS (18%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (EE 10%nat 10%bv) by (lia || reflexivity). exact H10.
- rm_mreg HS (19%bv : bv 5) G; rewrite G. reflexivity.
- rm_mreg HS (20%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E2_32.
- rm_mreg HS (21%bv : bv 5) G; rewrite G; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  change (8 * Z.of_nat 0) with 0. rewrite Z.add_0_r. exact E2_244.
- rm_mreg HS (22%bv : bv 5) G; rewrite G. symmetry.
  apply (gs_reg_shadow_of E2 32 244 SHADOW_OFF (VAL (A_OBJ 3)) _ E2_32 E2_244); try (unfold SHADOW_OFF; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.add_0_r. reflexivity.
- rm_mreg HS (23%bv : bv 5) G; rewrite G. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute.
  reflexivity.
Qed.

End ent.

Set Printing Implicit.
Check (tread_members_specX (fx := fx) (rc := rc) (cp := cp) (PI := prh_img_A) (RL := RL)
  (L := A_prog_listing) (PA := PA) B ARx SK).
Unset Printing Implicit.
Theorem read_members_holds : tread_members_specX (fx := fx) (rc := rc) (cp := cp) (PI := prh_img_A)
  (RL := RL) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
unfold tread_members_specX.
intros ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own [HPRE [HROD [HTOP [HRAZ HFRM]]]] H10 Hnode Hrs HLED.
exact (rm_body ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own HPRE HROD Hnode Hrs HLED HFRM H10).
Qed.
End w.
Set Printing Implicit.
Check read_members_holds.
Unset Printing Implicit.
Print Assumptions read_members_holds.
