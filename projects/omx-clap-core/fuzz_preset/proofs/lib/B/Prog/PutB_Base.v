(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), the
   program walk of put (preset_file.c :454-477; B' entry B_prog_sigma AS_put, 153 instructions of the whole-program
   listing lib/B/Listing_prog.v c97cc46b3e13 / PAImg_prog.v 15fab93fe702), toward the kit's text tput_specX of the batch kit's
   cut 7cdbb61b5fa0 (lib/A/PRH_FnWriter.v d89d3c67b78, tput_specX :410-499), generic
   :410-499), generic in the image instance (Context PAImg B_prog_listing) and in the allocator relation ARx (its laws AR_laws_x).
   THIS FILE: the walk's names, its ONE bundle of Section premises (putb_env, each field with its owner and its
   witness at the instance), and the walk's run-free lemmas (memory transfer, ledger, model, the entry and seat
   states, fuzz_realloc's call and post, the memcpy source after the call). The runs are in PutB_Loop.v,
   PutB_Tail.v, PutB_Arms.v; the theorem in PutB.v.
   rule 24: proves function put. proof-index put (index 2026-10-29T16:10:25Z, lemma index
   17:33:31Z): `put: 16 named, 699 by address, 114 related, 241 released lemma(s), delivery: 320 named and 12486 name(s)
   holding it, 89 UNRELEASED file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads`; no B / B'
   walk of put against a current text (second-agent check: CONFIRM). TEMPLATE (ported, not cited): the image-A walk
   lib/A/Prog/S7a_put.v (sha256 f576f7636d50; internal record) (its grow-success tail was never built).
   B' vs old B: bytecmp 1480ca2faea0 EQUAL-mod-pcrel (15, 0, 0), target pass 42/42 identical (RELOCATE-ONLY).
   B' vs A (what this port changes, measured on neutral listings): entry + 0x3c `andi a0, a0, 7; bnez -> unimp`
   (UBSan alignment of o); o + 24 in s4, o >> 3 in s3, o + 8 in s6 (spilled at 0(sp) across fuzz_realloc and
   reloaded); the need in a0 (A: a2); the copy block reads len through s6 and re-checks the shadow of o and o + 8 after
   __asan_memcpy; UBSan pointer-overflow / null checks at entry + 0x124 / + 0x134 (buf + len) and + 0x168 / + 0x178 /
   + 0x17c (buf + len + n), each trapping to `unimp` at entry + 0x1e4.
   THE RE-HIDING MOVE AND THE HULL (the texts' current form): fuzz_realloc's text concludes SRr' segs RZ_cf (a
   realloc of a live block frees the old block) with its post fpostmR at wle' segs RZ_cf, and takes the hull budget
   PresetHullBudget.hull_budget S Eg of its one event Eg; its post states the hull use and its refusal arm is
   world-free. put_realloc_call is the call rule over R (YCbqGcall.aj_call_x_spR) at wle' segs RZ_cf: the caller's
   plain journal is lifted there at the call (YCbqG.ajournal_xwR_mono), the budget is the env's pe_hull at put's run
   position (a run of at most 4 calls, put's new entry premise). put_realloc_Q is the text's post body, verbatim.
   Numerals: slot offsets are DERIVED (4 * index from put's entry slot, measured on the listing); 112 (LENGTH: put's
   frame, pi_frame F_put at prh_img_B), 8 / 16 / 24 / 32 (LENGTH: the fields of struct pj_out), 13 (the saved
   registers), atom indices (DERIVED: registers below 32, extra atoms from 32, after-call bands from 48 / 64 / 66);
   4096, 2 ^ 28, 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64, 0x7fff8000 (DERIVED bounds / SHADOW_OFF). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YG0dcf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetLiveBounds PresetRun PresetReqAt
  PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia never sees a division here: each x / 8 is named and bounded first (set ... ; clearbody) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- put's place in the generated listing ---- *)
Definition PUT_SLOT : nat := B_prog_slot AS_put.
Definition PUT_K : Z := 4 * Z.of_nat PUT_SLOT.
(* program points: index deltas from put's entry, measured on the B' listing (the B' addresses in comments are reading
   aids: entry 0x877d4).
   44 the need test `bgeu a1, a0` (0x87884); 46 `bnez a1` (0x8788c); 48 the doubling loop head `mv s6, a1`
   (0x87894); 51 after the loop (0x878a0); 56 `jal fuzz_realloc` (0x878b4), 57 its return site (0x878b8); 65 the
   JOIN `add s11, s3, s7` (0x878d8), the SEAT of the shared tail; 73 / 77 the UBSan checks of buf + len (0x878f8 /
   0x87908); 80 `jal __asan_memcpy` (0x87914); 90 / 94 / 95 the UBSan checks of buf + len + n (0x8793c / 0x8794c /
   0x87950); 100 the NUL store (0x87964); 115 the return (0x879a0); 116 the NULL arm (0x879a4). *)
Definition PK (j : Z) : Z := PUT_K + 4 * j.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).

Definition put_Bx : sv := SOff 32 0.
Definition put_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the ENTRY state: the struct pj_out at o = a0 (atom 10): buf, len, cap at 0 / 8 / 16 (atoms 33 / 34 / 35), failed at
   24 (a literal: the walk splits on failed = 0 / failed = 1 before it starts), all 32 bytes writable (the caller's
   window) *)
Definition put_struct (fl : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 32 0 32
    [ YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
      YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SLit fl)) ].
Definition put_regions (fl : Z) : smem :=
  [ stack_region (pi_frame F_put); got_regionP; bcell_regionP 32; put_struct fl ].
Definition put_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition put_ss (fl : Z) : sstate := mkSS PUT_K sr_atoms (put_regions fl) None put_facts.
(* the ONE shadow entry: the struct's 32 bytes; it decides every ASan check on the struct statically *)
Definition put_SH : list shent := [ mkSHE 10 0 32 ].
(* a proposition lia does not look into *)
Definition put_hide (P : Prop) : Prop := P.
Definition put_extra (buf len cap : Z) : list word :=
  [ Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap ].
Definition put_E (regs : bvmap 5 word) (buf len cap : Z) : env := Eimg (Ereg regs (put_extra buf len cap)).

(* ---- the SEAT at index 65 (`add s11, s3, s7`, the join of the no-grow and the grow arm): every register its own
   atom (s0 = o atom 8, s1 = n atom 9, s2 = s atom 18, s7 = the shadow base atom 23, sp atom 2 = the entry sp - 112)
   EXCEPT the three the tail reads as functions of o: s3 = o >> 3, s6 = o + 8, s8 = ((o + 8) >> 3) + s7 (so the
   engine decides the tail's shadow checks of o and o + 8 by the struct's shadow entry). put's frame READ-ONLY with
   the thirteen saved registers of the entry as atoms 35 .. 47 (ra, s0, s1, s2 .. s11); the struct at o with buf,
   len, cap as atoms 32 / 33 / 34 and failed = 0, writable. Facts: buf in [4096, 2 ^ 47] and len, n in [0, 2 ^ 47]
   (the tail's UBSan checks of buf + len / buf + len + n read them). ---- *)
Definition put_saved (regs : bvmap 5 word) : list word :=
  [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22;
    getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27 ].
Definition put_seat_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 112 0 0
    [ YP09.mkChunk 8 (CVal 8 (SOff 47 0)); YP09.mkChunk 16 (CVal 8 (SOff 46 0));
      YP09.mkChunk 24 (CVal 8 (SOff 45 0)); YP09.mkChunk 32 (CVal 8 (SOff 44 0));
      YP09.mkChunk 40 (CVal 8 (SOff 43 0)); YP09.mkChunk 48 (CVal 8 (SOff 42 0));
      YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
      YP09.mkChunk 72 (CVal 8 (SOff 39 0)); YP09.mkChunk 80 (CVal 8 (SOff 38 0));
      YP09.mkChunk 88 (CVal 8 (SOff 37 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0));
      YP09.mkChunk 104 (CVal 8 (SOff 35 0)) ].
Definition put_seat_struct : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 32 0 32
    [ YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
      YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SLit 0)) ].
Definition put_sv_s3 : sv := SAlu ALU_SRL (SOff 8 0) (SLit 3).
Definition put_sv_s6 : sv := SOff 8 8.
Definition put_sv_s8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 23 0).
Definition put_seat_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 19%bv put_sv_s3) 22%bv put_sv_s6) 24%bv put_sv_s8.
Definition put_seat_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
            (9%nat, mkAF 0 (2 ^ 47) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 0 (2 ^ 47) 0) ] [] [].
Definition put_ssk (k : Z) : sstate := mkSS k put_seat_regs [put_seat_frame; put_seat_struct] None put_seat_facts.
Definition put_Bx7 : sv := SOff 23 0.
Definition put_SH7 : list shent := [ mkSHE 8 0 32 ].
Definition put_Es (regs1 regs : bvmap 5 word) (bufx len capx : Z) : env :=
  Eimg (Ereg regs1 ([Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs)).

(* the return pc of put's `jal fuzz_realloc` (index 57) is a listing slot, below the ceiling: fpre's raZ bound at the
   call (PutB_Kit.pa_slot_lt_ceil_b), CLOSED so its vm_compute never runs inside a big proof *)
Lemma put_ret_slot_ceil : BASE + PK 57 < YM05.alloc_ceiling.
Proof.
let v := eval vm_compute in (PK 57) in
replace (PK 57) with v by (vm_compute; reflexivity);
exact (pa_slot_lt_ceil_b (PL := PL_prog_B) (PI := PA) v ltac:(lia) ltac:(vm_compute; reflexivity)).
Qed.

(* ---- THE WALK'S PREMISES, one bundle (every field is a Section hypothesis of PutB.v's theorem, where each is named
   with its owner; each has its witness at the instance in PutB.v): ---- *)
Record putb_env (B : asyms) (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
  : Prop := mkPutBEnv {
  (* the allocator relation's laws (at ARcf: PALibB.exvi_eh_laws) *)
  pe_laws : AR_laws_x SEGS B ARx cf_head;
  (* the image's runtime facts (owner the core; at TfibB: PALibB.exvi_eh_palib) *)
  pe_tl : PALib B;
  (* the entry: put's pc is its listing slot (at PI_prog_B by vm_compute) *)
  pe_ent : SIGMA AS_put = BASE + PUT_K;
  (* the GOT word (A_OBJ 0) and the shadow cell (A_OBJ 12) lie in the image's segments (at PI_prog_B: B_prog_obj_img) *)
  pe_obj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i);
  (* CALLEE TEXT, owner the fuzz_realloc B' lane (the kit's text at the batch kit's cut 7cdbb61b5fa0, lib/A/PRH_FnAlloc.v
     preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record), lib/A/PRH_FnAlloc.v (sha256 295647182d69; internal record) :412-509) *)
  pe_real : tfuzz_realloc_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK;
  (* THE HULL BUDGET of pe_real (route (b)): at a position of a run of at most 4 calls, room for one call's event of
     any admissible request (at CfParams_preset: PresetHullPay.hull_budget_of_room_pos with hull_nt_one_mal / _re) *)
  pe_hull : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk) S m r,
    (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S -> 0 <= r < cf_malloc_max ->
    PresetHullBudget.hull_budget S [PresetReqAt.HMal r] /\ PresetHullBudget.hull_budget S [PresetReqAt.HRe m r];
  (* RUNTIME ROW of __asan_memcpy with its memnorm keep (YGcallMxmn.aintrin_realizes_xm; owner the runtime
     rows) *)
  pe_amc : YGcallMxmn.aintrin_realizes_xm SEGS B ARx OCpy (SIGMA AS___asan_memcpy);
  (* the image's shadow bytes are visible (img_shadow_vis_cf over ARx, at the instance's bounds) *)
  pe_imgsh : ARx_img_shadow_vis_r SEGS ARx pa_lo pa_hi;
  (* every live fake frame's shadow hull is visible (the frame hull law over ARx) *)
  pe_frsh : ARx_frame_hull_vis SEGS ARx;
  (* alloc.c / fuzz_preset.c's seven statics are image bytes (at PI_prog_B by vm_compute over prh_img_B) *)
  pe_pst : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img SEGS a;
  (* The named head fact (PRH_Base.prh_head_wide; at CfParams_preset: preset_head_wide) *)
  pe_hw : prh_head_wide;
  (* no read-only image byte is a program static (at PI_prog_B by vm_compute) *)
  pe_pstro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B);
  (* the image's zero-shadow ranges are 8-aligned (at TfibB by vm_compute) *)
  pe_zsa : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B);
  (* fuzz_realloc's two live counts at a state that has the model-run position (counts_of_room_pos_rl,
     lib/Spec/PresetRoomCounts.v, at CfParams_preset) *)
  pe_cnt : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
    YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV;
  (* a live fake frame has a nonnegative class (alx_frames_cid, AR_laws_x field 19, landing with the
     P'' engine; at ARcf from its frame table) *)
  pe_fcid : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
    0 <= cid }.

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis HE : putb_env B ARx.
Let LAWS : AR_laws_x SEGS B ARx cf_head := pe_laws B ARx HE.
Let TL : PALib B := pe_tl B ARx HE.
Let HW : prh_head_wide := pe_hw B ARx HE.

(* a byte range of the real stack has zero shadow in every ARx state (LAWS' alx_zshadow_byte) *)
Lemma put_stack_ra : forall ly S Hp W mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.

(* ---- memory transfer of the writer state: a stretch that keeps every byte below alloc_ceiling keeps the buffer, its
   bytes and its shadow; the fields are the new state's ---- *)
Lemma put_out_kept : forall (W : world SEGS) mem mem' Lam o buf (st st' : WriterApp.wst),
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling) ->
  WriterApp.w_text st' = WriterApp.w_text st -> WriterApp.w_cap st' = WriterApp.w_cap st ->
  (WriterApp.w_failed st' = 0 \/ WriterApp.w_failed st' = 1) ->
  (WriterApp.w_failed st' = 0 -> WriterApp.w_failed st = 0) ->
  val_mem SEGS (mrestrict (w_H W) mem') o 8 buf ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 8) 8 (Z.of_nat (length (WriterApp.w_text st'))) ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 16) 8 (WriterApp.w_cap st') ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 24) 4 (WriterApp.w_failed st') ->
  prhWriter_out (PA := PA) W mem Lam o buf st -> prhWriter_out (PA := PA) W mem' Lam o buf st'.
Proof.
intros W mem mem' Lam o buf st st' Hlow Hbuf Etx Ecap Hf01' Hf0 V0' V8' V16' V24'
  (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VM : forall a n v, (forall k, (k < n)%nat -> aview SEGS (w_H W) mem' (a + Z.of_nat k) = aview SEGS (w_H W) mem (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hk Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros k Hk'. rewrite <- (Z2Nat.id k) by lia. apply Hk. lia. }
unfold prhWriter_out. rewrite Etx, Ecap in *.
split; [exact Ho8|]. split; [exact Hbr|]. split; [exact Hcr|].
split; [exact V0'|]. split; [exact V8'|]. split; [exact V16'|]. split; [exact V24'|].
split; [exact Hf01'|]. split; [exact Hbok|].
destruct Harm as [Hz | (Hgrid & Hin & Hlen & (rest & Hrl & Hba) & Hsh)]; [left; exact Hz|].
assert (Hcap0 : WriterApp.w_cap st <> 0).
{ destruct Hgrid as (j & Hj & Hc). intros Hz. rewrite Hz in Hc.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
destruct (Hbuf Hcap0) as (Hb0 & Hbc).
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [exact Hlen|].
split.
{ exists rest. split; [exact Hrl|]. intros j Hj. destruct (Hba j Hj) as (Hv & Hr). split; [|exact Hr].
  eapply VM; [intros kk Hkk; apply Hlow; cbn [length] in Hj; lia | exact Hv]. }
intros Hnf. destruct (Hsh (Hf0 Hnf)) as (Hra & Hhv). split.
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr, SHADOW_OFF. apply Hlow.
  set (q := x / 8) in *.
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (Hq8 : 8 * q <= x) by (unfold q; apply Z.mul_div_le; lia).
  clearbody q. lia.
- intros s Hs. rewrite Hlow; [apply (Hhv s Hs)|].
  unfold shadow_addr, shadow_of_addr, SHADOW_OFF in Hs |- *.
  set (q1 := buf / 8) in *. set (q2 := (buf + WriterApp.w_cap st - 1) / 8) in *.
  assert (Hq10 : 0 <= q1) by (unfold q1; apply Z.div_pos; lia).
  assert (Hq18 : 8 * q1 <= buf) by (unfold q1; apply Z.mul_div_le; lia).
  assert (Hq20 : 0 <= q2) by (unfold q2; apply Z.div_pos; lia).
  assert (Hq28 : 8 * q2 <= buf + WriterApp.w_cap st - 1) by (unfold q2; apply Z.mul_div_le; lia).
  clearbody q1 q2.
  set (r1 := (2147450880 + q1) / 8) in *. set (r2 := (2147450880 + q2) / 8) in *.
  assert (Hr10 : 0 <= r1) by (unfold r1; apply Z.div_pos; lia).
  assert (Hr18 : 8 * r1 <= 2147450880 + q1) by (unfold r1; apply Z.mul_div_le; lia).
  assert (Hr20 : 0 <= r2) by (unfold r2; apply Z.div_pos; lia).
  assert (Hr28 : 8 * r2 <= 2147450880 + q2) by (unfold r2; apply Z.mul_div_le; lia).
  clearbody r1 r2. lia.
Qed.

(* a 16-aligned address strictly below a 16-aligned ceiling leaves 8 bytes below it *)
Lemma put_al16_room : forall p c, p mod 16 = 0 -> c mod 16 = 0 -> p < c -> p + 8 <= c.
Proof.
intros p c Hp Hc Hlt.
pose proof (Z.div_mod p 16 ltac:(lia)) as Ep. pose proof (Z.div_mod c 16 ltac:(lia)) as Ec.
rewrite Hp in Ep. rewrite Hc in Ec.
set (qp := p / 16) in *. set (qc := c / 16) in *. clearbody qp qc. lia.
Qed.

(* the statics' cells lie below alloc_ceiling (they are image bytes, pe_pst) *)
Lemma put_pst_low : forall i w, In (i, w) (@prh_pst prh_img_B) -> forall k, 0 <= k < w ->
  0 <= i + k < YM05.alloc_ceiling.
Proof.
intros i w Hin k Hk. pose proof (@alloc_ceiling_value rc) as ((HC1 & _) & _).
assert (Hx : Exists (in_zr (i + k)) (@prh_pst prh_img_B)).
{ apply Exists_exists. exists (i, w). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
pose proof (pa_segs_low _ (pe_pst B ARx HE _ Hx)) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.

(* the ledger over a stretch that keeps every byte below alloc_ceiling *)
Lemma put_ledger_kept0 : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran most own HAR Hlow (Hg & Hnd & Hbl & Hperm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as (HCV1 & HCV2).
assert (VM : forall a (n : nat) v, (forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < YM05.alloc_ceiling) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hr Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros k Hk. rewrite <- (Z2Nat.id k) by lia. apply Hlow. apply Hr. lia. }
(* a static's cells: in prh_pst, so below the ceiling *)
assert (ST : forall i (n : nat), In (i, Z.of_nat n) (@prh_pst prh_img_B) ->
  forall k, (k < n)%nat -> 0 <= i + Z.of_nat k < YM05.alloc_ceiling).
{ intros i n Hin k Hk. apply (put_pst_low i (Z.of_nat n) Hin). lia. }
destruct Hg as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gr).
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G1]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G2]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G3]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G4]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G5]|].
  split; [split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G6] | exact G6r]|].
  split; [split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G7] | exact G7r]|].
  exact Gr.
- eapply Forall_impl; [|exact Hbl]. intros [a k] (Hk0 & Hin & HinHp & Ha16 & Hv). cbn [fst snd] in *.
  split; [exact Hk0|]. split; [exact Hin|]. split; [exact HinHp|]. split; [exact Ha16|].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin) as (Hp16 & Hp4 & Hpc & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hrs : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbv iota; lia).
  assert (H8 : a - cf_head + 8 <= YM05.alloc_ceiling).
  { apply put_al16_room; [exact Hp16 | | lia].
    pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(lia)) as Ec. rewrite HCV2 in Ec.
    rewrite Ec. set (q := YM05.alloc_ceiling / 4096). clearbody q.
    replace (4096 * q + 0) with ((256 * q) * 16) by lia. apply Z_mod_mult. }
  eapply VM; [intros kk Hkk; lia | exact Hv].
Qed.

(* the writer's buffer, when there is one, lies below alloc_ceiling (its block is a live allocator block) *)
Lemma put_buf_low : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own o buf (st : WriterApp.wst),
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  WriterApp.w_cap st <> 0 ->
  cf_head <= buf - 4096 /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling /\ buf mod 16 = 0 /\
  In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own o buf st HAR HLED HOUT Hc.
destruct HLED as (_ & _ & Hbl & _).
destruct HOUT as (_ & _ & Hcr & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction|].
pose proof (proj1 (Forall_forall _ _) Hbl _ Hin) as (Hk0 & Hinb & _ & Ha16 & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hinb) as (Hp16 & Hp4 & Hpc & _).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
rewrite Hreq in Hpc. split; [lia|]. split; [lia|]. split; [exact Ha16 | exact Hinb].
Qed.

(* ---- the entry state of the walk ---- *)
Lemma put_entry : forall ly S Hp W regs mem md ch o d buf len cap fl,
  afn_pre_x SEGS B ARx STK_put ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d -> o mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) o 8 buf -> 0 <= buf < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 8) 8 len -> 0 <= len < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 16) 8 cap -> 0 <= cap < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 24) 4 fl -> 0 <= fl < 2 ^ 32 ->
  st_ok_pi SEGS VAL (put_E regs buf len cap) (put_ss fl)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + PUT_K)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx put_SH (put_E regs buf len cap) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch o d buf len cap fl HAP H10 HWIN Hol Hoh Ho8 Vb Rb Vl Rl Vc Rc Vf Rf.
pose proof HAP as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : 112 <= STK_put) by (vm_compute; discriminate).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_val_range (A_OBJ 0)) as RG. pose proof (pa_val_range (A_OBJ 12)) as RC.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_segs_low (VAL (A_OBJ 0) + 7) (proj1 (pe_obj B ARx HE 7 ltac:(lia)))) as LG.
pose proof (pa_segs_low (VAL (A_OBJ 12) + 7) (proj2 (pe_obj B ARx HE 7 ltac:(lia)))) as LC.
rewrite restrict_mkst_fx.
set (E := put_E regs buf len cap).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len cap)) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold put_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold put_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Ho64 : 0 <= o < 2 ^ 64) by lia.
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
split.
- unfold put_ss. apply pa_entry_st_ok_full.
  + unfold E, put_E. apply (regs_ok_agree 32 (Ereg regs (put_extra buf len cap))).
    * split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + unfold put_regions, stack_region, got_regionP, bcell_regionP, put_struct. rewrite HKf.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 put_Bx SHADOW_OFF);
        [cbn [sv_denot put_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat o E10 Ho64). split; [lia|]. split; [lia|].
      split; [intros a Ha; apply (apresent_writable SEGS); apply Hdpres; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ o 0 8 (SOff 33 0) buf);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; apply unsigned_lit_small in Rb; reflexivity
         | zside | zside | rewrite Z.add_0_r; exact Vb].
      -- apply (chunk_ok_val SEGS E _ o 8 8 (SOff 34 0) len);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vl].
      -- apply (chunk_ok_val SEGS E _ o 16 8 (SOff 35 0) cap);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vc].
      -- apply (chunk_ok_val SEGS E _ o 24 4 (SLit fl) fl);
         [cbn [sv_denot]; reflexivity | zside | zside | exact Vf].
  + apply pairwise_disjoint_of_extents.
    unfold put_regions, stack_region, got_regionP, bcell_regionP, put_struct, extent_of_region. rewrite HKf.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat o E10 Ho64).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowMemEnd in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [put_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E10, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, put_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E put_Bx 10 o 32 o 0 32).
  + apply (put_stack_ra ly S Hp W mem md o 32 HAR); lia.
  + unfold U, put_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the shadow address of an atom plus an offset, as the engine forms it (`addi; srli 3; add` the shadow base) *)
Lemma put_denot_shx : forall E n m off v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb ->
  0 <= v -> 0 <= off -> v + off < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n off) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + off) / 8).
Proof.
intros E n m off v sb Hn Hm Hv0 Hoff Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n off) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n off) (SLit 3)) (SOff m 0)) = sb + (v + off) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + off) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + off) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v + off)) by (unfold M64; lia). rewrite (zcanon_id ((v + off) / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma put_denot_srl3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = Z_to_bv 64 (v / 8).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma put_denot_off : forall E n v off, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= off -> v + off < 2 ^ 64 ->
  sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn Hv0 Hoff Hv. cbn [sv_denot]. rewrite Hn. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- the seat (put_ssk k) from the concrete facts at the join ---- *)
Lemma put_seat : forall k (W : world SEGS) (regs regs1 : bvmap 5 word) mem1 bufx len capx n,
  spZ regs1 mod 16 = 0 -> 2 ^ 46 <= spZ regs1 -> spZ regs1 + 112 <= bv_unsigned (getr regs1 8) ->
  (forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1 + 104 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))) ->
  bv_unsigned (getr regs1 8) mod 8 = 0 -> bv_unsigned (getr regs1 8) + 32 <= 2 ^ 47 ->
  (forall a, bv_unsigned (getr regs1 8) <= a < bv_unsigned (getr regs1 8) + 32 -> apresent (w_H W) mem1 a) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8)) 8 bufx -> 4096 <= bufx <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 8) 8 len -> 0 <= len <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 16) 8 capx -> 0 <= capx < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 24) 4 0 ->
  getr regs1 23 = Z_to_bv 64 SHADOW_OFF -> getr regs1 9 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 47 ->
  getr regs1 19 = Z_to_bv 64 (bv_unsigned (getr regs1 8) / 8) ->
  getr regs1 22 = Z_to_bv 64 (bv_unsigned (getr regs1 8) + 8) ->
  getr regs1 24 = Z_to_bv 64 (SHADOW_OFF + (bv_unsigned (getr regs1 8) + 8) / 8) ->
  range_addressable (aview SEGS (w_H W) mem1) SHADOW_OFF (bv_unsigned (getr regs1 8)) 32 ->
  st_ok_pi SEGS VAL (put_Es regs1 regs bufx len capx) (put_ssk k)
    (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 (BASE + k)) mem1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx7 put_SH7 (put_Es regs1 regs bufx len capx) (mrestrict (w_H W) mem1).
Proof.
intros k W regs regs1 mem1 bufx len capx n Hal Hsp Hso Hsv Ho8 Ho47 Hopres Vb Rb Vl Rl Vc Rc Vf H23 H9 Hn
  H19 H22 H24 Hora.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (o := bv_unsigned (getr regs1 8)) in *.
set (xs := [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs).
set (E := put_Es regs1 regs bufx len capx).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 xs) kk)
  by (intros kk Hk; subst E; unfold put_Es; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (E8 : ew E 8 = getr regs1 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 8 8%bv eq_refl)).
assert (Uo : bv_unsigned (ew E 8) = o) by (rewrite E8; reflexivity).
assert (E8' : ew E 8 = Z_to_bv 64 o) by (rewrite E8; subst o; symmetry; apply Z_to_bv_bv_unsigned).
assert (E9 : ew E 9 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact H23).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 xs j)).
assert (Ho64 : 0 <= o < 2 ^ 64) by (subst o; apply u64_range).
assert (VB8 : base_val E (Some 8%nat) = o) by (cbn [base_val]; exact Uo).
assert (VB2 : base_val E (Some 2%nat) = spZ regs1) by (cbn [base_val]; exact Usp).
assert (CH : forall j, (j < 13)%nat -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem1) (spZ regs1)
   (YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ regs1) (104 - 8 * Z.of_nat j) 8 (SOff (35 + j) 0)
    (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
  - cbn [sv_denot]. rewrite Z.add_0_r. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite EX by lia. subst xs. rewrite app_nth2 by (cbn [length]; lia).
    replace (3 + j - length [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx])%nat with j by (cbn [length]; lia).
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - exact (u64_range (nth j (put_saved regs) (Z_to_bv 64 0))).
  - cbn. lia.
  - replace (spZ regs1 + (104 - 8 * Z.of_nat j)) with (spZ regs1 + 104 - 8 * Z.of_nat j) by lia. exact (Hsv j Hj). }
assert (DEN : forall (j : nat) z, (j < 3)%nat -> nth j xs (Z_to_bv 64 0) = Z_to_bv 64 z -> sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 z).
{ intros j z Hj Hz. cbn [sv_denot]. rewrite EX by lia. rewrite Hz, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 bufx) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (EX 1%nat ltac:(lia)).
split.
- unfold put_ssk. apply pa_entry_st_ok_full.
  + unfold put_seat_regs.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [|intros X; discriminate X|]|intros X; discriminate X|]
      |intros X; discriminate X|].
    * unfold E, put_Es. apply (regs_ok_agree 32 (Ereg regs1 xs)).
      -- split; [intros kk Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
      -- vm_compute. reflexivity.
      -- apply regs_ok_Ereg.
    * unfold put_sv_s3. rewrite (put_denot_srl3 E 8 o E8') by lia. exact H19.
    * unfold put_sv_s6. rewrite (put_denot_off E 8 o 8 E8') by lia. exact H22.
    * unfold put_sv_s8. rewrite (put_denot_shx E 8 23 8 o SHADOW_OFF E8' E23) by (unfold SHADOW_OFF; lia).
      exact H24.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold region_ok, put_seat_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      all: first [ exact (CH 12%nat ltac:(lia)) | exact (CH 11%nat ltac:(lia)) | exact (CH 10%nat ltac:(lia))
                 | exact (CH 9%nat ltac:(lia)) | exact (CH 8%nat ltac:(lia)) | exact (CH 7%nat ltac:(lia))
                 | exact (CH 6%nat ltac:(lia)) | exact (CH 5%nat ltac:(lia)) | exact (CH 4%nat ltac:(lia))
                 | exact (CH 3%nat ltac:(lia)) | exact (CH 2%nat ltac:(lia)) | exact (CH 1%nat ltac:(lia))
                 | exact (CH 0%nat ltac:(lia)) ].
    * unfold region_ok, put_seat_struct. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB8. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply (apresent_writable SEGS); apply Hopres; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ o 0 8 (SOff 32 0) bufx);
         [apply (DEN 0%nat); [lia | reflexivity] | zside | zside | rewrite Z.add_0_r; exact Vb].
      -- apply (chunk_ok_val SEGS E _ o 8 8 (SOff 33 0) len);
         [apply (DEN 1%nat); [lia | reflexivity] | zside | zside | exact Vl].
      -- apply (chunk_ok_val SEGS E _ o 16 8 (SOff 34 0) capx);
         [apply (DEN 2%nat); [lia | reflexivity] | zside | zside | exact Vc].
      -- apply (chunk_ok_val SEGS E _ o 24 4 (SLit 0) 0); [cbn [sv_denot]; reflexivity | zside | zside | exact Vf].
  + apply pairwise_disjoint_of_extents.
    unfold put_seat_frame, put_seat_struct, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB8, VB2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [put_seat_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uo, E23, E9, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, put_SH7. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem1 E put_Bx7 8 o 32 o 0 32).
  + exact Hora.
  + unfold U, put_Bx7. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E8', Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the struct's shadow entry at any ARx state: the struct lies on the real stack, whose shadow is zero *)
Lemma put_shok : forall (E' : env) ly S Hp (W : world SEGS) m md o,
  ARx ly S Hp W m md -> ew E' 32 = Z_to_bv 64 SHADOW_OFF -> ew E' 10 = Z_to_bv 64 o ->
  ly_stk_lo ly <= o -> o + 32 <= ly_stk_hi ly -> YM05.alloc_ceiling <= o -> o + 32 <= 2 ^ 47 ->
  sh_ok SEGS put_Bx put_SH E' (mrestrict (w_H W) m).
Proof.
intros E' ly S Hp W m md o HAR E32 E10 Hlo Hhi Ho0 Ho47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, put_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E' put_Bx 10 o 32 o 0 32).
- apply (put_stack_ra ly S Hp W m md o 32 HAR); lia.
- unfold U, put_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the shadow byte of an address below the stack band is itself below it, and so is a shadow hull there *)
Lemma put_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma put_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
(* a byte of value 0 *)
Lemma put_aview_val1 : forall (H : word -> bool) m a, val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a Hv. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
vm_compute. reflexivity.
Qed.

(* ---- the byte windows of the writer, read through the walk's view ---- *)
Lemma put_bytes_ok_of : forall (W : world SEGS) m p l, bytes_at (PA := PA) W m p l -> WriterSpec.bytes_ok l.
Proof. intros W m p l H. exact (garr8_bytes_ok SEGS (mrestrict (w_H W) m) p l H). Qed.

Lemma put_garr8_aview : forall (W : world SEGS) m p l j, bytes_at (PA := PA) W m p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold bytes_at in H. unfold aview.
rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

Lemma put_garr8_of_aview : forall (W : world SEGS) m p l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0)) ->
  WriterSpec.bytes_ok l -> bytes_at (PA := PA) W m p l.
Proof.
intros W m p l HA Hok. unfold bytes_at, garr8. intros j Hj.
assert (Hr : 0 <= nth j l 0 < 256) by exact (proj1 (Forall_forall _ _) Hok _ (nth_In l 0 Hj)).
split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (HA j Hj). unfold aview in HA.
destruct (mbyte SEGS (mrestrict (w_H W) m) (p + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA;
  [|discriminate HA].
injection HA as Hb. f_equal.
rewrite (YI04.le_byte_small (nth j l 0) 1 0) by (try (change (2 ^ (8 * Z.of_nat 1)) with 256); lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the writer state after a put that copied bs at buf' + len and stored the NUL *)
Lemma put_out_put : forall (W1 : world SEGS) mem1 mem' Lam' o buf' cap' (text bs : list Z) r0 (rest : list Z) s
    cnt' fail' calls',
  o mod 8 = 0 -> 4096 <= buf' -> buf' + cap' <= YM05.alloc_ceiling ->
  (buf' + cap' <= kLowShadowBeg \/ kHighMemBeg <= buf') ->
  (exists j, 0 <= j <= 51 /\ cap' = 4096 * 2 ^ j) -> In (buf', cap') Lam' ->
  Z.of_nat (length (text ++ r0 :: rest)) = cap' ->
  bytes_at (PA := PA) W1 mem1 buf' (text ++ r0 :: rest) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF buf' cap' ->
  shadow_hull_vis (aview SEGS (w_H W1) mem1) buf' cap' ->
  WriterSpec.bytes_ok text ->
  bytes_at (PA := PA) W1 mem1 s bs ->
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= cap' ->
  (forall a, 0 <= a < YM05.alloc_ceiling ->
     ~ (buf' + Z.of_nat (length text) <= a <= buf' + Z.of_nat (length text) + Z.of_nat (length bs)) ->
     aview SEGS (w_H W1) mem' a = aview SEGS (w_H W1) mem1 a) ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     aview SEGS (w_H W1) mem' (buf' + Z.of_nat (length text) + i) = aview SEGS (w_H W1) mem1 (s + i)) ->
  aview SEGS (w_H W1) mem' (buf' + Z.of_nat (length text) + Z.of_nat (length bs)) = Some 0 ->
  val_mem SEGS (mrestrict (w_H W1) mem') o 8 buf' ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 8) 8 (Z.of_nat (length text) + Z.of_nat (length bs)) ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 16) 8 cap' ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 24) 4 0 ->
  prhWriter_out (PA := PA) W1 mem' Lam' o buf' (WriterApp.mkW 0 (text ++ bs) cap' cnt' fail' calls').
Proof.
intros W1 mem1 mem' Lam' o buf' cap' text bs r0 rest s cnt' fail' calls' Ho8 Hb4096 Hbc Hband Hgrid Hin Hlen Hba
  Hra Hhv Htok Hbs Hroom Hkeep Hcopy Hnul V0 V8 V16 V24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlen' : Z.of_nat (length text) + 1 + Z.of_nat (length rest) = cap')
  by (rewrite <- Hlen, length_app; cbn [length]; lia).
assert (NS : forall (l : list Z) m i, nth i (skipn m l) 0 = nth (m + i) l 0).
{ intros l. induction l as [|x l IH]; intros [|m] i; cbn; try reflexivity; try (destruct i; reflexivity). apply IH. }
assert (D8 : forall z, 0 <= z -> 0 <= z / 8 /\ 8 * (z / 8) <= z < 8 * (z / 8) + 8).
{ intros z Hz. pose proof (Z.div_mod z 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as M.
  pose proof (Z.div_pos z 8 Hz ltac:(lia)) as P.
  set (qq := z / 8) in *. set (rr := z mod 8) in *. clearbody qq rr. lia. }
unfold prhWriter_out. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap].
split; [exact Ho8|]. split; [lia|]. split; [lia|].
split; [exact V0|]. split; [rewrite length_app, Nat2Z.inj_add; exact V8|].
split; [exact V16|]. split; [exact V24|]. split; [left; reflexivity|].
split; [unfold WriterSpec.bytes_ok; apply Forall_app; split; [exact Htok | exact (put_bytes_ok_of W1 mem1 s bs Hbs)]|].
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [rewrite length_app; lia|].
split.
- exists (skipn (length bs) rest). split.
  + rewrite !length_app. cbn [length]. rewrite length_skipn. lia.
  + apply put_garr8_of_aview.
    * intros j Hj. rewrite !length_app in Hj. cbn [length] in Hj. rewrite length_skipn in Hj.
      destruct (Nat.lt_ge_cases j (length text)) as [J1 | J1].
      { rewrite Hkeep by lia.
        rewrite (put_garr8_aview W1 mem1 buf' (text ++ r0 :: rest) j Hba) by (rewrite length_app; cbn [length]; lia).
        rewrite (app_nth1 text (r0 :: rest) 0 J1), <- app_assoc.
        rewrite (app_nth1 text (bs ++ 0 :: skipn (length bs) rest) 0 J1). reflexivity. }
      destruct (Nat.lt_ge_cases j (length text + length bs)) as [J2 | J2].
      { replace (buf' + Z.of_nat j) with (buf' + Z.of_nat (length text) + Z.of_nat (j - length text)) by lia.
        rewrite (Hcopy (Z.of_nat (j - length text))) by lia.
        rewrite (put_garr8_aview W1 mem1 s bs (j - length text) Hbs) by lia.
        rewrite (app_nth1 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := j)) by (rewrite length_app; lia).
        rewrite (app_nth2 text bs 0 J1). reflexivity. }
      destruct (Nat.eq_dec j (length text + length bs)) as [J3 | J3].
      { subst j. rewrite Nat2Z.inj_add, Z.add_assoc, Hnul.
        rewrite (app_nth2 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := length text + length bs))
          by (rewrite length_app; lia).
        rewrite length_app, Nat.sub_diag. reflexivity. }
      { rewrite Hkeep by lia.
        rewrite (put_garr8_aview W1 mem1 buf' (text ++ r0 :: rest) j Hba) by (rewrite length_app; cbn [length]; lia).
        rewrite (app_nth2 text (r0 :: rest) 0 J1).
        rewrite (app_nth2 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := j)) by (rewrite length_app; lia).
        rewrite length_app.
        replace (j - length text)%nat with (S (j - length text - 1)) by lia.
        replace (j - (length text + length bs))%nat with (S (j - (length text + length bs) - 1)) by lia.
        cbn [nth]. rewrite NS. f_equal. f_equal. lia. }
    * pose proof (put_bytes_ok_of W1 mem1 buf' _ Hba) as Hob.
      pose proof (put_bytes_ok_of W1 mem1 s bs Hbs) as Hobs.
      unfold WriterSpec.bytes_ok in *.
      apply Forall_app in Hob as [_ Hob]. apply Forall_cons_iff in Hob as [_ Hob].
      rewrite <- (firstn_skipn (length bs) rest) in Hob. apply Forall_app in Hob as [_ Hob].
      apply Forall_app. split; [apply Forall_app; split; [exact Htok | exact Hobs]|].
      constructor; [cbv beta; lia | exact Hob].
- intros _. split.
  + eapply range_addressable_agree; [|exact Hra]. intros x Hx.
    destruct (D8 x ltac:(lia)) as (Qa & Qb & Qc).
    apply Hkeep; unfold shadow_of_addr, SHADOW_OFF; set (q := x / 8) in *; clearbody q;
      unfold kLowShadowBeg, kHighMemBeg in Hband; destruct Hband; lia.
  + intros s0 Hs0. rewrite Hkeep; [exact (Hhv s0 Hs0) | |];
      unfold shadow_addr, SHADOW_OFF in Hs0;
      destruct (D8 buf' ltac:(lia)) as (Q1a & Q1b & Q1c); set (q1 := buf' / 8) in *; clearbody q1;
      destruct (D8 (buf' + cap' - 1) ltac:(lia)) as (Q2a & Q2b & Q2c);
      set (q2 := (buf' + cap' - 1) / 8) in *; clearbody q2;
      destruct (D8 (2147450880 + q1) ltac:(lia)) as (R1a & R1b & R1c);
      set (r1 := (2147450880 + q1) / 8) in *; clearbody r1;
      destruct (D8 (2147450880 + q2) ltac:(lia)) as (R2a & R2b & R2c);
      set (r2 := (2147450880 + q2) / 8) in *; clearbody r2;
      unfold kLowShadowBeg, kHighMemBeg in Hband; destruct Hband; lia.
Qed.

(* the ledger over a stretch that changes only the user bytes [b, b + k) of one ledger block (and nothing else below
   alloc_ceiling): the statics are image bytes (pe_pst), no block byte is (YCbqG blk_img_x), and every other ledger head
   is in another block (alx_blocks: the blocks are pairwise disjoint) *)
Lemma put_ledger_copy : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran most own b k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (b, k) Lam ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (b <= a < b + k) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran most own b k HAR (Hg & Hnd & Hbl & Hperm) Hbk Hkeep.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof HW as HW8. unfold prh_head_wide in HW8.
destruct (proj1 (Forall_forall _ _) Hbl _ Hbk) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in Hk0, Hinb.
assert (Hrqb : req_size (k + cf_head) = k + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbv iota; lia).
assert (NIMG : forall a, b <= a < b + k -> ~ in_img SEGS a).
{ intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (k + cf_head) a HAR Hinb).
  rewrite Hrqb. lia. }
assert (VM : forall a (n : nat) v, (forall kk, (kk < n)%nat ->
    0 <= a + Z.of_nat kk < YM05.alloc_ceiling /\ ~ (b <= a + Z.of_nat kk < b + k)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hr Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros kk Hkk. rewrite <- (Z2Nat.id kk) by lia.
  destruct (Hr (Z.to_nat kk) ltac:(lia)) as (Hr1 & Hr2). apply Hkeep; [exact Hr1 | exact Hr2]. }
assert (ST : forall i (n : nat), In (i, Z.of_nat n) (@prh_pst prh_img_B) ->
  forall kk, (kk < n)%nat -> 0 <= i + Z.of_nat kk < YM05.alloc_ceiling /\ ~ (b <= i + Z.of_nat kk < b + k)).
{ intros i n Hin kk Hkk. split; [apply (put_pst_low i (Z.of_nat n) Hin); lia|].
  intros Hr. apply (NIMG _ Hr). apply (pe_pst B ARx HE). apply Exists_exists. exists (i, Z.of_nat n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
destruct Hg as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gr).
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G1]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G2]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G3]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G4]|].
  split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G5]|].
  split; [split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G6] | exact G6r]|].
  split; [split; [eapply VM; [apply ST; unfold prh_pst; cbn [In]; tauto | exact G7] | exact G7r]|].
  exact Gr.
- eapply Forall_impl; [|exact Hbl]. intros [a k'] (Hk0' & Hin' & HinHp & Ha16 & Hv). cbn [fst snd] in *.
  split; [exact Hk0'|]. split; [exact Hin'|]. split; [exact HinHp|]. split; [exact Ha16|].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin') as (Hp16 & Hp4 & Hpc & _).
  assert (Hrq : req_size (k' + cf_head) = k' + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); cbv iota; lia).
  rewrite Hrq in Hpc.
  eapply VM; [|exact Hv]. intros kk Hkk. split; [lia|].
  destruct (Z.eq_dec a b) as [-> | Hne]; [lia|].
  assert (Hne2 : (a - cf_head, k' + cf_head) <> (b - cf_head, k + cf_head)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin' Hinb Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, Hrqb in Hd. lia.
Qed.

(* a doubling step of the capacity: `slli a1, a1, 1` on a small value *)
Lemma put_sll1 : forall c, 0 <= c < 2 ^ 62 -> alu64 ALU_SLL (Z_to_bv 64 c) (Z_to_bv 64 1) = Z_to_bv 64 (2 * c).
Proof.
intros c Hc. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small c), (Z.mod_small 1) by lia. change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

(* a fresh register-only seat (the doubling loop touches no memory) *)
Definition put_ssr (k : Z) : sstate := mkSS k sr_atoms [] None (mkFacts [] [] []).

Lemma put_seat_r : forall k (W1 : world SEGS) (regs1 : bvmap 5 word) mem1,
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (put_ssr k)
    (restrict (w_H W1) (YK11.mkst regs1 (Z_to_bv 64 (BASE + k)) mem1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx [] (Eimg (Ereg regs1 [])) (mrestrict (w_H W1) mem1).
Proof.
intros k W1 regs1 mem1. split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold put_ssr. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

(* a shadow hull of a window covers the hull of a sub-window *)
Lemma put_hull_sub : forall (rd : reader) p m d k, shadow_hull_vis rd p m -> p <= d -> d + k <= p + m -> 0 < k ->
  shadow_hull_vis rd d k.
Proof.
intros rd p m d k Hh Hpd Hdn Hn s0 Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + k - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* a byte window survives a change that keeps its bytes *)
Lemma put_bytes_keep : forall (W : world SEGS) m m' p l, bytes_at (PA := PA) W m p l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m' (p + Z.of_nat j) = aview SEGS (w_H W) m (p + Z.of_nat j)) ->
  bytes_at (PA := PA) W m' p l.
Proof.
intros W m m' p l H Hk. apply put_garr8_of_aview; [|exact (put_bytes_ok_of W m p l H)].
intros j Hj. rewrite (Hk j Hj). exact (put_garr8_aview W m p l j H Hj).
Qed.

(* newcap's base: 4096 when there is no buffer yet *)
Lemma put_newcap0 : forall need, WriterSpec.newcap 0 need = WriterSpec.dbl 64 4096 need.
Proof. intros need. unfold WriterSpec.newcap. rewrite Z.eqb_refl. reflexivity. Qed.

(* ---- the grown capacity is on the 4096 * 2 ^ j grid and covers the need ---- *)
Lemma put_dbl_grid : forall f j need, 0 <= j -> need <= 4096 * 2 ^ (j + Z.of_nat f) ->
  exists j', j <= j' /\ WriterSpec.dbl f (4096 * 2 ^ j) need = 4096 * 2 ^ j' /\ need <= 4096 * 2 ^ j'.
Proof.
induction f as [|f IH]; intros j need Hj Hn.
- exists j. cbn [WriterSpec.dbl Z.of_nat] in *. rewrite Z.add_0_r in Hn. split; [lia|]. split; [reflexivity | exact Hn].
- cbn [WriterSpec.dbl]. destruct (Z.leb_spec need (4096 * 2 ^ j)) as [Hle | Hgt].
  + exists j. split; [lia|]. split; [reflexivity | exact Hle].
  + replace (2 * (4096 * 2 ^ j)) with (4096 * 2 ^ (j + 1)) by (rewrite Z.pow_add_r by lia; ring).
    destruct (IH (j + 1) need ltac:(lia)) as (j' & Hj' & E & Hn').
    { replace (j + 1 + Z.of_nat f) with (j + Z.of_nat (Datatypes.S f)) by (rewrite Nat2Z.inj_succ; lia). exact Hn. }
    exists j'. split; [lia|]. split; [exact E | exact Hn'].
Qed.

Lemma put_newcap_grid : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= 2 ^ 28 ->
  (exists j, 0 <= j <= 51 /\ WriterSpec.newcap c need = 4096 * 2 ^ j) /\ need <= WriterSpec.newcap c need /\
  WriterSpec.newcap c need <= 2 ^ 28 /\ c <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn.
pose proof (WriterSpecFacts.newcap_le28 c need Hc Hn) as H28.
assert (G : exists j, 0 <= j /\ c <= 4096 * 2 ^ j /\ WriterSpec.newcap c need = WriterSpec.dbl 64 (4096 * 2 ^ j) need).
{ destruct Hc as [-> | (j & Hj & ->)].
  - exists 0. split; [lia|]. split; [lia|]. unfold WriterSpec.newcap. rewrite Z.eqb_refl. reflexivity.
  - exists j. split; [lia|]. split; [lia|]. unfold WriterSpec.newcap.
    assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    rewrite (proj2 (Z.eqb_neq _ 0)) by lia. reflexivity. }
destruct G as (j & Hj & Hcj & EG).
assert (Hb : need <= 4096 * 2 ^ (j + Z.of_nat 64)).
{ assert (1 <= 2 ^ j) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hj; lia).
  rewrite Z.pow_add_r by lia. change (2 ^ Z.of_nat 64) with 18446744073709551616. nia. }
destruct (put_dbl_grid 64 j need Hj Hb) as (j' & Hj' & E & Hn'). rewrite <- EG in E.
assert (Hj51 : j' <= 51).
{ destruct (Z_le_gt_dec j' 51) as [H | H]; [exact H|]. exfalso.
  assert (2 ^ 52 <= 2 ^ j') by (apply Z.pow_le_mono_r; lia). lia. }
split; [exists j'; split; [lia | exact E]|]. split; [rewrite E; exact Hn'|]. split; [exact H28|].
rewrite E. assert (2 ^ j <= 2 ^ j') by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* read-only image bytes survive a journal *)
Lemma put_arodata_kept : forall STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k HJ Hsk HRO a Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HRO a Hro Hown Herr) | | exact Hown | exact Herr | exact (pe_pstro B ARx HE a Hro)
  | exact (fp_spares_closed FP a Hsk)].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)].
Qed.

(* ---- fuzz_realloc's post: the post of the text tfuzz_realloc_specX (PRH_FnAlloc.v, the anonymous post of its
   fpostmR), by its name in the text's projection layer, PRH_FnAlloc.tfrP_Q (tfrP_Q_check fails to build if that body
   and the text's post ever differ); this name only puts the arguments in the walk's order. POST-IMPLICATION form: the
   position transfer is an implication over the model run at the arm's own event list (NULL: []; grant at p = 0:
   [HMal (n + cf_head)]; grant at p <> 0: [HRe (k + cf_head) (n + cf_head)]); the OUTCOME clauses: at a consumer
   allocation (prh_cons_from) of a run whose next event is the granted one, with cnt <> fail, res <> 0. The hull use is
   the text's third conjunct (tfrP_hull); the refusal arm is world-free. Consumers read it through the layer's named
   projections (tfrP_R_of, the arm records tfrP_R1 .. tfrP_R4), never by position. ---- *)
Definition put_realloc_Q (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) ly S
  (Hp : list Z) (W : world SEGS) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own.

(* ---- THE ONE CALL OF fuzz_realloc: the kit's tfuzz_realloc_specX (pe_real) through the engine's call rule over R,
   aj_call_x_spR, at wle' segs RZ_cf (the text concludes SRr' segs RZ_cf): the caller's plain journal is lifted to wle'
   here, at the cut before the call; both journals after it are at wle' ---- *)
Lemma put_realloc_call : forall W E ss ms STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k (o' : Z) raw ch1
    p kk nn (old : list Z) Lam peak cnt fail ran most own,
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_realloc ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o' -> o' mod 16 = 0 -> o' <= 0 -> STK_fuzz_realloc - o' <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o') (s0Z (ms_regs ms)) ch1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms)) ->
  spZ (ms_regs ms) + 64 <= ly_stk_hi lyc -> raZ (ms_regs ms) < YM05.alloc_ceiling -> YK0o.frm_zero (@YK11.fp_csr fx) ->
  room_live_cf Sc -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt Sc <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget Sc
    (if p =? 0 then [PresetReqAt.HMal (nn + cf_head)] else [PresetReqAt.HRe (kk + cf_head) (nn + cf_head)]) ->
  In [cf_pc_realloc_ra0] (u_fix (as_universe B)) ->
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)) ->
  getr (ms_regs ms) 10 = w64 p -> getr (ms_regs ms) 11 = w64 nn -> 0 <= nn -> nn + cf_head < cf_malloc_max ->
  prh_ledger B lyc Sc Hpc W (ms_mem ms) Lam peak cnt fail ran most own ->
  (p = 0 /\ kk = 0 /\ old = [] \/ In (p, kk) Lam /\ bytes_at W (ms_mem ms) p old /\ Z.of_nat (length old) = kk) ->
  (cnt <> fail -> blocks_bytes Sc + (nn + cf_head) <= LIVE_MAX) ->
  fp_sub_x B STK sp0 FP (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) ly S [] lyc Sc ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP
        ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
      ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK_fuzz_realloc (sp0 + o')
        (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) lyc Sc Hpc W (ms_mem ms) mdc []
        ly2 S2 Hp2 W2 mem2 md2 k1 /\
      aregs_preserved (ms_regs ms) regs2 /\
      fQmn (ms_mem ms) (put_realloc_Q p kk nn old Lam peak cnt fail ran most own lyc Sc Hpc W) ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k o' raw ch1 p kk nn old Lam peak cnt fail ran most own
  HS Hrv HPC HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hch HRO HTOP HRAZ HFRM HROOM HMU HSEC H24 HHULL HU1 HU2 H10 H11
  Hn0 Hnmax HLED HOLD HLIVE HF.
assert (HK2 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
(* the caller's journal, lifted from wle to wle' segs RZ_cf (wle_wle') *)
pose proof (ajournal_xwR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJR.
apply (aj_call_x_spR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low _ _ PA)
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
  W E ss ms STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc mdc k STK_fuzz_realloc
  (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) o' raw ch1
  (fQmn (ms_mem ms) (put_realloc_Q p kk nn old Lam peak cnt fail ran most own lyc Sc Hpc W))
  HS Hrv HJR Hsp Hal Hneg HK2 Hbud Hgp Htp Hra Hraw Hra4 Hch);
  [|exact HF].
intros HAPc. rewrite HPC.
(* the callee's fpre: put's own afn_pre_x at the call, its read-only bytes, its stack top, the jal's return pc below the
   ceiling and the entry rounding mode (FRM0-ENTRY: the class position fx is put's, unchanged across put); its hull
   budget is the caller's *)
exact (pe_real B ARx HE lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 p kk nn old Lam peak cnt fail ran most own
  (conj HAPc (conj HRO (conj HTOP (conj HRAZ HFRM)))) HROOM HMU HSEC H24 HHULL HU1 HU2 H10 H11 Hn0 Hnmax HLED HOLD
  HLIVE).
Qed.

(* ---- THE POSITION through the leaf's post implications ---- *)
(* the leaf's NULL arm gives the position at i + 0 with SOME hist' (PRH_FnAlloc.v 4d8aeba047e :437-440); put's batch kit
   text asks exactly that on its grow-NULL outcome (`f' = 1 -> exists hist', ..`, PRH_FnWriter.v d89d3c67b78 :493, the
   form the kit took from this walk's former _FIX twin, NULL-HIST) *)
Lemma putb_null_pos : forall (S S' : astate) (rp_sm : list Z -> Z * Z) (rp_x : list Z)
    (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S'.
Proof.
intros S S' rp_sm rp_x rp_os rp_i rp_H0 rp_hist HN HP.
destruct (HN rp_sm rp_x rp_os rp_i rp_H0 rp_hist HP eq_refl) as (hist' & H').
exists hist'. cbn [length] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.
(* a grant's one event: the caller's nth_error supply (put's text premise) is the leaf's prh_run_at at one event
   (PRH_Base.prh_run_at_one), and the advance is one *)
Lemma putb_grant_pos : forall (S S' : astate) (rp_sm : list Z -> Z * Z) (rp_x : list Z)
    (rp_os : list (option nat * option nat * option nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk)
    (ev : PresetReqAt.hev),
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [ev] ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [ev])%nat H0 hist' S') ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some ev ->
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S'.
Proof.
intros S S' rp_sm rp_x rp_os rp_i rp_H0 rp_hist ev HG HP HEv.
destruct (HG rp_sm rp_x rp_os rp_i rp_H0 rp_hist HP (proj2 (PRH_Base.prh_run_at_one rp_sm rp_x rp_os rp_i ev) HEv))
  as (hist' & H').
exists hist'. cbn [length] in H'. rewrite Nat.add_1_r in H'. exact H'.
Qed.

(* ---- fuzz_realloc's post, sorted by the returned a0: NULL or a new block res. At put's grow the NULL is the
   allocation set to fail ONLY (DEAD-PUT): the call is a consumer allocation (the text's prh_cons_from, here HCONS)
   whose next event is the granted one (the text's run premise, here HRUN), so at cnt <> fail the leaf's OUTCOME
   clause gives res <> 0, which refutes both of its REFUSED arms (p = 0: prh_alloc_post's; p <> 0: the third
   disjunct). The grant's position follows from HRUN by the leaf's position clause. ---- *)
Lemma put_realloc_cases : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z)
    (rp_os : list (option nat * option nat * option nat)) (rp_H0 : list Z) (rp_i : nat) (rp_hist : list YG00.chunk)
    buf cap nc (old : list Z) Lam peak cnt fail ran most own ly S Hp (W : world SEGS)
    ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (buf = 0 /\ cap = 0 /\ old = [] \/ buf <> 0 /\ cap <> 0) -> 0 <= cap < nc ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (cnt <> fail -> nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i =
     Some (if cap =? 0 then PresetReqAt.HMal (nc + cf_head) else PresetReqAt.HRe (cap + cf_head) (nc + cf_head))) ->
  (cnt <> fail -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 1) ->
  put_realloc_Q buf cap nc old Lam peak cnt fail ran most own ly S Hp W ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  room_live_cf S2 /\
  ((bv_unsigned (getr regs2 10) = 0 /\ Permutation Hp2 Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
    (buf <> 0 -> bytes_at W2 mem2 buf old) /\
    cnt = fail /\ prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own /\
    exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S2)
   \/
   (exists res, bv_unsigned (getr regs2 10) = res /\ cnt <> fail /\
    4096 + cf_head <= res /\ res mod 16 = 0 /\ res + nc <= YM05.alloc_ceiling /\
    exists l1 l2 b1 b2,
      ((cap = 0 /\ l1 = [] /\ l2 = Lam /\ b1 = [] /\ b2 = ablocks B ly S) \/
       (cap <> 0 /\ Lam = l1 ++ (buf, cap) :: l2 /\ ablocks B ly S = b1 ++ (buf - cf_head, cap + cf_head) :: b2)) /\
      Permutation (ablocks B ly2 S2) ((res - cf_head, nc + cf_head) :: b1 ++ b2) /\
      (exists rest, bytes_at W2 mem2 res (firstn (Z.to_nat (Z.min cap nc)) old ++ rest) /\
         Z.of_nat (length rest) = nc - Z.min cap nc) /\
      range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF res nc /\
      (0 < nc -> shadow_hull_vis (aview SEGS (w_H W2) mem2) res nc) /\
      ~ In res (map fst (l1 ++ l2)) /\
      prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, nc) :: l1 ++ l2) (Z.max peak (Ledger.lsum (l1 ++ l2) + nc))
        ((cnt + 1) mod 2 ^ 64) fail ran most own /\
      exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S2)).
Proof.
intros rp_sm rp_x rp_os rp_H0 rp_i rp_hist buf cap nc old Lam peak cnt fail ran most own ly S Hp W ly2 S2 Hp2 W2 regs2
  mem2 md2 HAR2 Hbc Hnc HPOS HRUN HCONS HQ.
(* the post read through the text's named projections (PRH_FnAlloc's tfrP_R and its arm records), never by position *)
unfold put_realloc_Q in HQ.
destruct (tfrP_R_of HQ) as (res & HQR).
pose proof (tfrP_ret HQR) as Hres. pose proof (tfrP_room HQR) as HR2. pose proof (tfrP_pos_null HQR) as HP0.
pose proof (tfrP_pos_malloc HQR) as HPM. pose proof (tfrP_pos_realloc HQR) as HPR.
pose proof (tfrP_outcome_malloc HQR) as HOM. pose proof (tfrP_outcome_realloc HQR) as HOR.
assert (HNP : res = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S2)
  by (intros Hr0; exact (putb_null_pos S S2 rp_sm rp_x rp_os rp_i rp_H0 rp_hist (HP0 Hr0) HPOS)).
(* the run premise at the leaf's one event, in its prh_run_at form *)
assert (HRA : cnt <> fail -> PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i
  [if cap =? 0 then PresetReqAt.HMal (nc + cf_head) else PresetReqAt.HRe (cap + cf_head) (nc + cf_head)])
  by (intros Hcf; exact (proj2 (PRH_Base.prh_run_at_one rp_sm rp_x rp_os rp_i _) (HRUN Hcf))).
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U0 : res = 0 -> bv_unsigned (getr regs2 10) = 0) by (intros ->; rewrite Hres; vm_compute; reflexivity).
assert (UB : forall b n', In (b, n') (ablocks B ly2 S2) -> b = res - cf_head -> n' = nc + cf_head ->
  bv_unsigned (getr regs2 10) = res /\ res + nc <= YM05.alloc_ceiling).
{ intros b n' Hin -> ->. destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin) as (_ & H4 & Hc & _).
  assert (Hreq : req_size (nc + cf_head) = nc + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0); cbv iota; lia).
  rewrite Hreq in Hc. split; [|lia]. rewrite Hres. apply unsigned_lit_small. lia. }
split; [exact HR2|].
destruct (tfrP_arm HQR) as [HA | [HA | [HA | HA]]].
1: pose proof (tfrP_R1_of HA) as HA1; pose proof (tfrP1_null HA1) as Hp0; pose proof (tfrP1_alloc HA1) as HAP.
2: pose proof (tfrP_R2_of HA) as HA2; pose proof (tfrP2_nonnull HA2) as Hp0; pose proof (tfrP2_chosen HA2) as Hcf;
   pose proof (tfrP2_res0 HA2) as Hr0; pose proof (tfrP2_hp HA2) as EHp; pose proof (tfrP2_ablocks HA2) as Ebl;
   pose proof (tfrP2_bytes HA2) as Hba; pose proof (tfrP2_ledger HA2) as HL.
3: pose proof (tfrP_R3_of HA) as HA3; pose proof (tfrP3_nonnull HA3) as Hp0; pose proof (tfrP3_notchosen HA3) as Hcf;
   pose proof (tfrP3_res0 HA3) as Hr0.
4: destruct (tfrP_R4_of HA) as (l1 & l2 & HA4); pose proof (tfrP4_nonnull HA4) as Hp0;
   pose proof (tfrP4_notchosen HA4) as Hcf; pose proof (tfrP4_res_min HA4) as Hr4; pose proof (tfrP4_res_align HA4) as Hr16;
   pose proof (tfrP4_lam HA4) as EL; pose proof (tfrP4_fresh HA4) as Hnin; pose proof (tfrP4_hp HA4) as EHp;
   destruct (tfrP4_ablocks HA4) as (b1 & b2 & Eb & _ & Pb); destruct (tfrP4_bytes HA4) as (rest & Hlr & Hbr);
   pose proof (tfrP4_addressable HA4) as Hra; pose proof (tfrP4_hull HA4) as Hhv; pose proof (tfrP4_ledger HA4) as HL.
- destruct Hbc as [(Hb0 & Hc0 & Ho0) | (Hb0 & _)]; [|contradiction].
  rewrite Hc0, Z.eqb_refl in HRA.
  unfold prh_alloc_post in HAP.
  destruct HAP as [(Hcf & Hr0 & EHp & Ebl & HL) | [(Hcf & Hr0 & EHp & Ebl & _ & _ & HL) |
    (Hcf & Hr4 & Hr16 & Hnin & EHp & Ebl & Hra & Hhv & (l & Hll & Hbl) & HL)]].
  + left. split; [exact (U0 Hr0)|]. split; [rewrite EHp; apply Permutation_refl|]. split; [exact Ebl|].
    split; [intros H; contradiction|]. split; [exact Hcf|]. split; [exact HL | exact (HNP Hr0)].
  + (* the REFUSED arm of realloc (NULL, n): dead by the leaf's outcome clause *)
    exfalso.
    destruct (HOM Hp0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS (HRA Hcf) (HCONS Hcf) Hcf) as (Hrn & _).
    exact (Hrn Hr0).
  + right. destruct (UB (res - cf_head) (nc + cf_head)) as (Ur & Hrc); [rewrite Ebl; apply in_or_app; right; left; reflexivity | reflexivity | reflexivity |].
    exists res. split; [exact Ur|]. split; [exact Hcf|]. split; [lia|]. split; [exact Hr16|]. split; [exact Hrc|].
    exists [], Lam, [], (ablocks B ly S). split; [left; repeat split; assumption|].
    split; [rewrite Ebl; cbn [app]; apply Permutation_sym, Permutation_cons_append|].
    split; [exists l; rewrite Ho0, Hc0, firstn_nil; cbn [app]; split; [exact Hbl | lia]|].
    split; [exact Hra|]. split; [exact Hhv|]. split; [exact Hnin|]. split; [exact HL|].
    destruct (HPM ltac:(lia) Hp0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS (HRA Hcf)) as (hist' & H').
    exists hist'. cbn [length] in H'. rewrite Nat.add_1_r in H'. exact H'.
- left. split; [exact (U0 Hr0)|]. split; [rewrite EHp; apply Permutation_refl|]. split; [exact Ebl|].
  split; [intros _; exact Hba|]. split; [exact Hcf|]. split; [exact HL | exact (HNP Hr0)].
- (* the REFUSED arm of realloc (buf, n): dead by the leaf's outcome clause *)
  exfalso.
  destruct Hbc as [(Hb0 & _) | (_ & Hc0)]; [contradiction|].
  rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HRA.
  destruct (HOR Hp0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS (HRA Hcf) (HCONS Hcf) Hcf) as (Hrn & _).
  exact (Hrn Hr0).
- right. destruct (UB (res - cf_head) (nc + cf_head)) as (Ur & Hrc);
    [apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity | reflexivity | reflexivity |].
  exists res. split; [exact Ur|]. split; [exact Hcf|]. split; [lia|]. split; [exact Hr16|]. split; [exact Hrc|].
  destruct Hbc as [(Hb0 & _) | (_ & Hc0)]; [contradiction|].
  rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HRA.
  exists l1, l2, b1, b2. split; [right; split; [exact Hc0|]; split; [exact EL | exact Eb]|].
  split; [exact Pb|]. split; [exists rest; split; [exact Hbr | exact Hlr]|].
  split; [exact Hra|]. split; [exact Hhv|]. split; [exact Hnin|]. split; [exact HL|].
  destruct (HPR ltac:(lia) Hp0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS (HRA Hcf)) as (hist' & H').
  exists hist'. cbn [length] in H'. rewrite Nat.add_1_r in H'. exact H'.
Qed.

(* the model of a put that grows and whose fuzz_realloc returns NULL (outcome false): failed, text and cap kept *)
Lemma put_null_model : forall (st : WriterApp.wst) bs,
  WriterApp.w_failed st = 0 -> WriterApp.w_cap st < prhWriter_need st bs ->
  prhWriter_putN [false] st [bs] =
    WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64)
      (if WriterApp.w_cnt st =? WriterApp.w_fail st then 2 ^ 64 - 1 else WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]) /\
  prhWriter_k [false] st [bs] = 1%nat.
Proof.
intros st bs Hf Hc.
assert (Hg : prhWriter_grows st bs = true)
  by (unfold prhWriter_grows; rewrite Hf; cbn [Z.eqb andb]; apply Z.ltb_lt; exact Hc).
assert (E : prhWriter_putN [false] st [bs] =
    WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64)
      (if WriterApp.w_cnt st =? WriterApp.w_fail st then 2 ^ 64 - 1 else WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)])).
{ cbn [prhWriter_putN]. rewrite Hg. cbn [hd tl prhWriter_putN]. unfold prhWriter_put1. rewrite Hg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); reflexivity. }
split; [exact E|]. unfold prhWriter_k. rewrite E. cbn [WriterApp.w_calls]. rewrite length_app. cbn [length]. lia.
Qed.

(* the model of a put that grows and whose fuzz_realloc returns a block (outcome true, not the one set to fail) *)
Lemma put_grow_model : forall (st : WriterApp.wst) bs,
  WriterApp.w_failed st = 0 -> WriterApp.w_cap st < prhWriter_need st bs ->
  WriterApp.w_cnt st <> WriterApp.w_fail st ->
  prhWriter_putN [true] st [bs] =
    WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs))
      ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]) /\
  prhWriter_k [true] st [bs] = 1%nat.
Proof.
intros st bs Hf Hc Hcf.
assert (Hg : prhWriter_grows st bs = true)
  by (unfold prhWriter_grows; rewrite Hf; cbn [Z.eqb andb]; apply Z.ltb_lt; exact Hc).
assert (E : prhWriter_putN [true] st [bs] =
    WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs))
      ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)])).
{ cbn [prhWriter_putN]. rewrite Hg. cbn [hd tl prhWriter_putN]. unfold prhWriter_put1. rewrite Hg.
  rewrite (proj2 (Z.eqb_neq _ _) Hcf). reflexivity. }
split; [exact E|]. unfold prhWriter_k. rewrite E. cbn [WriterApp.w_calls]. rewrite length_app. cbn [length]. lia.
Qed.

(* ---- the memcpy source after fuzz_realloc ---- *)
(* a shadow hull of a read-only window away from the image's ends maps back into the image range [lo, hi) *)
Lemma put_hull_img : forall lo hi a n s0, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s0 < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s0 = shadow_addr (8 * (s0 - SHADOW_OFF)) /\ lo <= 8 * (s0 - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s0 Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
set (qa := a / 8) in *. set (qb := (a + n - 1) / 8) in *.
set (qc := (2147450880 + qa) / 8) in *. set (qd := (2147450880 + qb) / 8) in *.
set (ra := a mod 8) in *. set (rb := (a + n - 1) mod 8) in *.
set (rc' := (2147450880 + qa) mod 8) in *. set (rd' := (2147450880 + qb) mod 8) in *.
clearbody qa qb qc qd ra rb rc' rd'.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
Lemma put_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a registered zero-shadow global's bytes are addressable in every ARx state (zero-shadow law, pe_zsa) *)
Lemma put_zs_ra : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 q m,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> In (q, m) (as_zero_shadow B) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF q m.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 q m HAR Hin.
pose proof (proj1 (Forall_forall _ _) (pe_zsa B ARx HE) (q, m) Hin) as (Hq & Hm). cbn [fst snd] in Hq, Hm.
pose proof (alx_zshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (q, m) HAR
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
cbn [fst snd] in Hz.
exact (zero_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF q m Hq Hm Hz).
Qed.
(* the source after the call, from the call's journal at any world relation R (the call frees the old buffer, so the
   walk reads it at wle' segs RZ_cf; no step below reads the world conjunct) *)
Lemma put_src_after : forall (R : world SEGS -> world SEGS -> Prop)
    ly S Hp (W : world SEGS) mem md memc mdc ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 sp1
    Lam peak cnt fail ran most own buf cap s (bs : list Z) n res nc l1 l2 peak2 cnt2 fail2 ran2 most2 own2,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  src_rd (PA := PA) W mem s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B ly S Lam buf cap s n ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R STK_fuzz_realloc sp1
    (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (cap = 0 /\ buf = 0 /\ l1 = [] /\ l2 = Lam \/ cap <> 0 /\ Lam = l1 ++ (buf, cap) :: l2) ->
  In (res - cf_head, nc + cf_head) (ablocks B ly2 S2) -> ~ In (res - cf_head, nc + cf_head) (ablocks B ly S) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, nc) :: l1 ++ l2) peak2 cnt2 fail2 ran2 most2 own2 ->
  0 < nc ->
  bytes_at (PA := PA) W2 mem2 s bs /\
  (forall a, s <= a < s + n -> aview SEGS (w_H W2) mem2 a <> None) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W2) mem2) s n) /\
  (res + nc <= s \/ s + n <= res \/ n = 0).
Proof.
intros R ly S Hp W mem md memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 sp1 Lam peak cnt fail ran most own buf cap s bs n res nc l1 l2
  peak2 cnt2 fail2 ran2 most2 own2 HAR HLED HSRC Hn HHOME KLOWc HJin Harm HinN HnotN HL2 Hnc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof HSRC as (Sba & S4096 & Sceil & Samr & Sra & Shull). rewrite Hn in Sceil, Samr, Sra, Shull.
pose proof HJin as (HAR2 & Hly2 & _ & _ & _ & Hfr2 & _ & _ & G1 & G2 & G3 & G4 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md ly2 HAR Hly2) as (_ & Efa & _).
pose proof HLED as (_ & Hnd & Hbl & _).
assert (Hreqn : req_size (nc + cf_head) = nc + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0); cbv iota; lia).
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
{ destruct bs as [|b0 bs']; [|cbn in Hn; lia]. cbn in Hn. subst n.
  split; [apply put_garr8_of_aview; [intros j Hj; cbn in Hj; lia | exact (put_bytes_ok_of W mem s [] Sba)]|].
  split; [intros a Ha; lia|]. split; [intros x Hx; lia|]. split; [intros H; lia|]. right; right; reflexivity. }
assert (Hnp : 0 < n) by lia.
assert (HOLDB : buf <> 0 -> cap <> 0 /\ In (buf, cap) Lam /\ In (buf - cf_head, cap + cf_head) (ablocks B ly S) /\
  4096 <= buf - cf_head /\ req_size (cap + cf_head) = cap + cf_head).
{ intros Hb0. destruct Harm as [(_ & Hb0' & _) | (Hc0 & ELam)]; [contradiction|].
  assert (HinO : In (buf, cap) Lam) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Hbl (buf, cap) HinO) as (Hk0 & HabO & _). cbn [fst snd] in Hk0, HabO.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HabO) as (_ & H4 & _).
  split; [exact Hc0|]. split; [exact HinO|]. split; [exact HabO|]. split; [exact H4|].
  unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); cbv iota; lia. }
assert (HSK : ~ YI16.sink_open_fp (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)])).
{ destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [intros (r & [] & _)|].
  destruct (HOLDB Hb0) as (_ & _ & _ & H4 & _). apply sink_closed_pos. constructor; [cbn; lia | constructor]. }
destruct HHOME as (Hk & Hdisj).
assert (CASES : (forall a, s <= a < s + n -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF s n /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) s n /\ (res + nc <= s \/ s + n <= res)).
{ destruct Hk as [[(b & m & HinL & Hbs & Hbm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] |
    (cid & pos & Hfin & Hfs & Hfe)].
  - (* a live harness block other than the buffer *)
    pose proof (proj1 (Forall_forall _ _) Hbl (b, m) HinL) as (Hm0 & Hab & Hhp & Hb16 & _). cbn [fst snd] in *.
    assert (Hreq : req_size (m + cf_head) = m + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); cbv iota; lia).
    assert (HinL2 : In (b, m) (l1 ++ l2)).
    { destruct Harm as [(Hc0 & Hb0 & -> & ->) | (Hc0 & ELam)]; [exact HinL|].
      rewrite ELam in HinL. apply in_app_or in HinL as [H | [E | H]];
        [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
      inversion E; subst. destruct Hdisj as [Hz | [H1 | H1]]; lia. }
    pose proof HL2 as (_ & _ & Hbl2 & _).
    pose proof (proj1 (Forall_forall _ _) Hbl2 (b, m) (or_intror HinL2)) as (_ & Hab2 & Hhp2 & _). cbn [fst snd] in *.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb4 & Hbc & _). rewrite Hreq in Hbc.
    assert (NFP : forall a, b - cf_head <= a < b + m ->
      ~ inFP (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) a).
    { intros a Ha (r & Hr & Hra).
      destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [destruct Hr|].
      destruct (HOLDB Hb0) as (Hc0 & HinO & HabO & _ & HreqO).
      cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra. rewrite HreqO in Hra.
      assert (Hne : (b - cf_head, m + cf_head) <> (buf - cf_head, cap + cf_head)).
      { intros E. inversion E as [[E1 E2]]. assert (Ebb : b = buf) by lia. subst b.
        destruct Harm as [(Hc0' & _) | (_ & ELam)]; [contradiction|].
        rewrite ELam, map_app in Hnd. cbn [map] in Hnd. apply NoDup_ListNoDup in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
        rewrite <- map_app. apply in_map_iff. exists (buf, m). split; [reflexivity | exact HinL2]. }
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab HabO Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, HreqO in Hd. lia. }
    split.
    { intros a Ha. replace a with (b - cf_head + (a - (b - cf_head))) by lia.
      rewrite (G2 (b - cf_head) (m + cf_head) (a - (b - cf_head)) Hab Hab2 ltac:(rewrite Hreq; lia)
        ltac:(apply NFP; lia)).
      apply KLOWc. lia. }
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (b - cf_head) (m + cf_head) HAR2 Hab2 Hhp2)
      as (Hbsh & Hhv).
    rewrite Hreq in Hbsh, Hhv. replace (b - cf_head + cf_head) with b in Hbsh, Hhv by lia.
    replace (m + cf_head - cf_head) with m in Hbsh, Hhv by lia.
    split; [exact (block_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF b m s n Hbsh Hbs Hbm)|].
    split; [exact (put_hull_sub _ b m s n (Hhv ltac:(lia)) Hbs Hbm Hnp)|].
    assert (Hne2 : (b - cf_head, m + cf_head) <> (res - cf_head, nc + cf_head))
      by (intros E; rewrite E in Hab; exact (HnotN Hab)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hab2 HinN Hne2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hreqn in Hd. lia.
  - (* a registered zero-shadow read-only global *)
    split.
    { intros a Ha. destruct (Hro a Ha) as (Hr & Hown & Herr).
      rewrite (G3 a (put_ro_img a Hr) Hown Herr (pe_pstro B ARx HE a Hr) (fp_spares_closed _ a HSK)).
      apply KLOWc. pose proof (@pa_segs_low _ _ PA a (put_ro_img a Hr)). lia. }
    split.
    { destruct Hzs as (q & mq & Hinq & Hq1 & Hq2).
      apply (range_addressable_sub _ _ q mq s n); [exact (put_zs_ra ly2 S2 Hp2 W2 mem2 md2 q mq HAR2 Hinq) | lia | lia]. }
    split.
    { intros s0 Hs0.
      destruct (put_hull_img pa_lo pa_hi s n s0 Hnp Hlo Hhi Hs0) as (E & Hr).
      rewrite E. exact (pe_imgsh B ARx HE ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr). }
    destruct (Z_le_gt_dec (res + nc) s) as [h | h]; [left; exact h|].
    destruct (Z_le_gt_dec (s + n) res) as [h' | h']; [right; exact h'|].
    exfalso. set (x := Z.max s res).
    assert (Hxs : s <= x < s + n) by (unfold x; lia).
    assert (Hxr : res - cf_head <= x < res - cf_head + req_size (nc + cf_head)) by (rewrite Hreqn; unfold x; lia).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 HinN Hxr (put_ro_img x (proj1 (Hro x Hxs)))).
  - (* an image string with its exact shadow *)
    split.
    { intros a Ha. destruct (Hro a Ha) as (Hr & Hown & Herr & _).
      rewrite (G3 a (put_ro_img a Hr) Hown Herr (pe_pstro B ARx HE a Hr) (fp_spares_closed _ a HSK)).
      apply KLOWc. pose proof (@pa_segs_low _ _ PA a (put_ro_img a Hr)). lia. }
    split.
    { intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcell & Hv)]).
      - destruct Hzs as (q & mq & Hinq & Hq1 & Hq2). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
        exact (put_zs_ra ly2 S2 Hp2 W2 mem2 md2 q mq HAR2 Hinq x ltac:(lia)).
      - exists v. split; [|unfold saddr_ok; lia].
        pose proof (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR2) as HC.
        pose proof (proj1 (Forall_forall _ _) HC _ (Hcell ly2)) as Hh.
        unfold cell_holds, z1, c1 in Hh. cbn [c_at c_val c_w aeval] in Hh.
        specialize (Hh 0%nat ltac:(lia)). rewrite Z.add_0_r in Hh.
        unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). rewrite Hh. f_equal.
        unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
        pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
        rewrite (Z.mod_small v (2 ^ 8)) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
    split.
    { intros s0 Hs0.
      destruct (put_hull_img pa_lo pa_hi s n s0 Hnp Hlo Hhi Hs0) as (E & Hr).
      rewrite E. exact (pe_imgsh B ARx HE ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr). }
    destruct (Z_le_gt_dec (res + nc) s) as [h | h]; [left; exact h|].
    destruct (Z_le_gt_dec (s + n) res) as [h' | h']; [right; exact h'|].
    exfalso. set (x := Z.max s res).
    assert (Hxs : s <= x < s + n) by (unfold x; lia).
    assert (Hxr : res - cf_head <= x < res - cf_head + req_size (nc + cf_head)) by (rewrite Hreqn; unfold x; lia).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 HinN Hxr (put_ro_img x (proj1 (Hro x Hxs)))).
  - (* a live fake frame of the entry *)
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hf4 & Hfc & Hfapp).
    destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hf32 & _).
    pose proof (pe_fcid B ARx HE ly S Hp W mem md cid pos HAR Hfin) as Hcid.
    assert (Hfb : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (H2c : 1 <= 2 ^ cid) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    assert (Hfs8 : 8 <= fs_frame_bytes cid) by lia.
    assert (Hfm8 : fs_frame_bytes cid mod 8 = 0)
      by (rewrite Hfb; replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring; apply Z_mod_mult).
    set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
    assert (NFPf : forall a, fa <= a < fa + fb \/ (kLowShadowBeg <= a < kHighMemBeg) ->
      ~ inFP (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) a).
    { intros a Ha (r & Hr & Hra).
      destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [destruct Hr|].
      destruct (HOLDB Hb0) as (Hc0 & HinO & HabO & _ & HreqO).
      cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra. rewrite HreqO in Hra.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HabO) as (_ & _ & _ & HappO & _).
      rewrite HreqO in HappO.
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR HabO Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqO in Hd. fold fa fb in Hd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
    split.
    { intros a Ha.
      rewrite (G4 cid pos a Hfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold fa fb; lia)
        ltac:(apply NFPf; left; lia)).
      apply KLOWc. lia. }
    split.
    { intros x Hx. destruct (Sra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok]. rewrite <- Hv.
      set (qx := x / 8). set (qa := fa / 8). set (qf := fb / 8).
      assert (Hf8 : fa mod 8 = 0).
      { pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Hf32, Z.add_0_r in D. rewrite D.
        replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by ring. apply Z_mod_mult. }
      assert (Eqa : fa = 8 * qa) by (unfold qa; pose proof (Z.div_mod fa 8 ltac:(lia)); lia).
      assert (Eqf : fb = 8 * qf) by (unfold qf; pose proof (Z.div_mod fb 8 ltac:(lia)); lia).
      assert (Hqx : 8 * qx <= x < 8 * qx + 8)
        by (unfold qx; pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
      assert (Esh : shadow_of_addr SHADOW_OFF x = SHADOW_OFF + qx) by reflexivity.
      clearbody qx qa qf.
      rewrite Esh.
      rewrite (G4 cid pos (SHADOW_OFF + qx) Hfin).
      - apply KLOWc. unfold SHADOW_OFF. lia.
      - right. unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fb. rewrite Eqa, Eqf.
        rewrite (Z.mul_comm 8 qa), (Z.mul_comm 8 qf), !Z.div_mul by lia. lia.
      - apply NFPf. right. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF. lia. }
    split.
    { assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hfin).
      pose proof (pe_frsh B ARx HE ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 HinF2) as Hh. rewrite Efa in Hh. fold fa fb in Hh.
      exact (put_hull_sub _ fa fb s n Hh Hfs Hfe Hnp). }
    assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hfin).
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 HinN HinF2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqn, Efa in Hd. fold fa fb in Hd. lia. }
destruct CASES as (KEEPS & RA & HULL & DISJ).
assert (BYTES : bytes_at (PA := PA) W2 mem2 s bs).
{ apply put_garr8_of_aview; [|exact (put_bytes_ok_of W mem s bs Sba)].
  intros j Hj. rewrite KEEPS by lia. exact (put_garr8_aview W mem s bs j Sba Hj). }
split; [exact BYTES|].
split; [intros a Ha; rewrite KEEPS by exact Ha; replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia;
  rewrite (put_garr8_aview W mem s bs (Z.to_nat (a - s)) Sba ltac:(lia)); discriminate|].
split; [exact RA|]. split; [intros _; exact HULL|]. destruct DISJ as [D | D]; [left; exact D | right; left; exact D].
Qed.

(* a block's application range gives the ASan range of a window inside it, and its band *)
Lemma put_app_amem : forall p m q k, in_app p m -> p <= q -> 0 <= k -> q + k <= p + m -> amem_range q k.
Proof.
intros p m q k (H1 & H2) Hq Hk Hqk. pose proof (@ASAN_CEIL_range rc) as (HC & _).
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
Lemma put_app_band : forall b c h, in_app (b - h) (c + h) -> 0 <= h -> b + c <= kLowShadowBeg \/ kHighMemBeg <= b.
Proof. intros b c h (H1 & [H2 | (H2 & H3)]) Hh; [left; lia | right; lia]. Qed.

(* ---- the grown buffer's block is new ---- *)
Lemma put_pairwise_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hsym l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' HP1 IH1 HP2 IH2]; cbn; intros H.
- exact I.
- destruct H as (Hf & Hp). split; [|exact (IH Hp)].
  apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hf). exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as (Hf1 & Hf2 & Hp). apply Forall_cons_iff in Hf1 as (Hyx & Hf1).
  split; [constructor; [apply Hsym; exact Hyx | exact Hf2] | split; [exact Hf1 | exact Hp]].
- exact (IH2 (IH1 H)).
Qed.

Lemma put_newblk : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 (bl0 b1 b2 : list (Z * Z)) x old,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 < snd x ->
  Permutation (ablocks B ly2 S2) (x :: b1 ++ b2) ->
  (bl0 = b2 /\ b1 = [] \/ bl0 = b1 ++ old :: b2 /\ old <> x) ->
  ~ In x bl0.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 bl0 b1 b2 x old HAR Hx Pb Hbl Hin.
assert (Hinx : In x (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity).
destruct x as [p n]. cbn [snd] in Hx.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p n HAR Hinx) as (_ & _ & _ & _ & _ & Hpw).
pose proof (put_pairwise_perm zdisjoint (fun a b H => ltac:(unfold zdisjoint in *; lia)) _ _
  (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b))) Pb) Hpw) as Hpw'.
cbn [map pairwise] in Hpw'. destruct Hpw' as (Hf & _).
assert (Hnot : ~ In (p, n) (b1 ++ b2)).
{ intros H. pose proof (proj1 (Forall_forall _ _) Hf (p, req_size n)
    (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (p, n) H)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbv iota; lia). lia. }
destruct Hbl as [(-> & ->) | (-> & Hne)]; [exact (Hnot Hin)|].
apply in_app_or in Hin as [H | [E | H]];
  [apply Hnot; apply in_or_app; left; exact H | exact (Hne E) | apply Hnot; apply in_or_app; right; exact H].
Qed.

(* the failed field holds one value: a stored 1 is not a 0, a stored 0 is not a 1 (one byte decides) *)
Lemma put_val_mem_1 : forall (m : word -> option byte) a f, val_mem SEGS m a 4 f -> val_mem SEGS m a 4 1 -> f <> 0.
Proof.
intros m a f Hf H1 ->.
pose proof (Hf 0%nat ltac:(lia)) as B0. pose proof (H1 0%nat ltac:(lia)) as B1.
rewrite B0 in B1. injection B1 as B1. revert B1.
vm_compute. intro B1. discriminate B1.
Qed.
Lemma put_val_mem_0 : forall (m : word -> option byte) a f, val_mem SEGS m a 4 f -> val_mem SEGS m a 4 0 -> f <> 1.
Proof.
intros m a f Hf H0 ->.
pose proof (Hf 0%nat ltac:(lia)) as B1. pose proof (H0 0%nat ltac:(lia)) as B0.
rewrite B1 in B0. injection B0 as B0. revert B0.
vm_compute. intro B0. discriminate B0.
Qed.

(* ---- the record from o at the realloc call ---- *)
Lemma put_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
assert (G : forall k, 0 <= k < 8 -> exists b, rd (a + k) = Some b)
  by (intros k Hk; destruct (rd (a + k)) as [b|] eqn:E; [exists b; reflexivity | exfalso; exact (H k Hk E)]).
destruct (G 0 ltac:(lia)) as (b0 & E0). rewrite Z.add_0_r in E0.
destruct (G 1 ltac:(lia)) as (b1 & E1). destruct (G 2 ltac:(lia)) as (b2 & E2).
destruct (G 3 ltac:(lia)) as (b3 & E3). destruct (G 4 ltac:(lia)) as (b4 & E4).
destruct (G 5 ltac:(lia)) as (b5 & E5). destruct (G 6 ltac:(lia)) as (b6 & E6).
destruct (G 7 ltac:(lia)) as (b7 & E7).
rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.
Lemma put_apresent_aview : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma put_rdword_nonneg : forall (H : word -> bool) m a v, rdword (aview SEGS H m) a = Some v -> 0 <= v.
Proof.
intros H m a v Hv. unfold rdword, aview in Hv.
repeat match type of Hv with
  | context [option_map ?f (mbyte ?s ?mm ?x)] =>
      let b := fresh "b" in destruct (mbyte s mm x) as [b|]; cbn [option_map] in Hv;
      [pose proof (u8_range b) | discriminate Hv]
  end.
injection Hv as <-.
lia.
Qed.
Lemma put_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma put_rdword_ext : forall (rd rd' : reader) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma put_chain_one : forall ly (rd : reader) sp o ra nfp,
  YM05.alloc_ceiling <= o -> o mod 8 = 0 -> sp + 16 <= o -> o < ly_top ly - 16 ->
  rdword rd (o - 8) = Some ra -> 0 <= ra -> rdword rd (o - 16) = Some nfp -> nfp < YM05.alloc_ceiling ->
  exists ch, achain ly rd sp o ch.
Proof.
intros ly rd sp o ra nfp Hc Ho8 Hsp Htop Hra Hra0 Hnfp Hnc.
destruct (Z_lt_le_dec ra 4096) as [Hlt | Hge].
- exists []. right. split; [lia|]. split; [lia|]. split; [exact Ho8|]. split; [|constructor].
  cbn [fpchain]. exists ra. split; [exact Hra | lia].
- exists [(o, ra, nfp)]. right. split; [lia|]. split; [lia|]. split; [exact Ho8|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Hra|]. split; [exact Hnfp|].
    split; [exact Hge|]. unfold bad_next. rewrite (proj2 (Z.leb_le nfp o)) by lia. reflexivity.
  + constructor; [cbn; lia | constructor].
Qed.
End h.
End W.

(* ---- the walk's tactics (S7a_put.v's, unchanged) ---- *)
Ltac put_hide_all := repeat match goal with H : _ \/ _ |- _ => let T := type of H in change (put_hide T) in H end.
(* the write permission of a run's regions: the frame and the struct in the caller window (both inside
   [sp0 - STK, sp0), the window journal's own range), the GOT word and the shadow cell read-only *)
Ltac put_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with |- awr_ok ?Ex (YP09.mkRegion (Some ?m) _ _ _ _ _ :: _) _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (bv_unsigned (ew Ex m) - sp0')) end;
  [reflexivity | lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].
(* the region list of a symbolic state: the i-th region's region_ok at the state's memory *)
Ltac put_region HS i r H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?msr =>
    assert (H : region_ok segs E (ms_mem msr) r)
      by (exact (st_ok_region_nth segs E (abs_ss val ss) msr i r HS ltac:(vm_compute; reflexivity)));
    cbn [ms_mem restrict] in H
  end.
Ltac put_region_auto HS i H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem (abs_ss val ss)) in
    let r := eval cbn in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    put_region HS i r H
  end.
(* the region list of a symbolic state at a call stop (st_ok, not st_ok_pi) *)
Ltac put_region_auto_st HS i H :=
  lazymatch type of HS with st_ok ?segs ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem ss) in
    let r := eval cbn in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    assert (H : region_ok segs E (ms_mem msr) r)
      by (exact (st_ok_region_nth segs E ss msr i r HS ltac:(vm_compute; reflexivity)));
    cbn [ms_mem restrict] in H
  end.
