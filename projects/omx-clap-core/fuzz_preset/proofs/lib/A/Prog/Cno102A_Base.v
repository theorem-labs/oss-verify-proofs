(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 1214 of its 1315 lines of code are new or changed and 1889 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the SHARED
   CONTRACT of the re-walk of check_no_overread (cno, entry A_prog_slot AS_check_no_overread = slot 201, 388
   instructions) against K0's text tcheck_no_overread_specX. Lane CnoA102r (h-rw-pre-5, #102 plan
   the internal file PLAN-cno-caw-102.md sections 5.0 / 5.1). This file STATES; Cno102A_R.v (CA5-CA9, lane CnoA102r) and
   Cno102A_F.v (CA10-CA11, lane CnoA102f) prove segments over it; the CA0-CA4 lanes and the top compose.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (the kit's cut of record, owner 06:11Z; every path at the cut's blob
   but this lane's files): lib/A/PRH_Base.v (prh_univ_closure CTX0 without the run-word list DW,
   DW-SPLIT; fpre; fpostFb / fpostFbm, the posts at a wild budget; prh_wk F_check_no_overread = 6, F_parse_noting =
   2), lib/A/PRH_FnCheck.v c40cf3fdcd2a (tcheck_no_overread_specX :738-823, ck_cno_copies :264-266, ck_cno_evs
   :268-281, ck_cno_ranout :284-285, tparse_noting_specX: the reading's free-order tie :718-720), PRH_FnPj.v
   5aca5cbe2cfb, PRH_FnAlloc.v 4d8aeba047e5, PRH_FnEx.v, PRH_FnReader.v f1ae32e3b2cd, PRH_PjOrder.v
   e5917626b82b (pj_foR), PRH_Img.v 934516a622e8; the engine of the cut: lib/Reusable/YCbqG.v (ajournal_xw, the journal
   with the wild-trace list WS; ajournal_x is its WS = [] instance), YCbqGwild.v (wild_room, wbudget); the #102 model:
   PresetRun.v 5ac818ab1fe6, PresetReqAt.v 43c958024221, PresetReqAtNoMiss.v f949715d7a12.
     Listings of record: lib/A/Listing_prog.v, lib/A/PAImg_prog.v, lib/Reusable/YPsym.v at the cut's blobs (A_OBJ 13 =
     g_own_ran_out, A_OBJ 14 = g_most).
   PARAMETRIC over {PA : PAImg A_prog_listing} (owner 12:48Z): no image number is typed here. Offsets are DERIVED byte
   offsets inside check_no_overread (4 * slot), read off the A' disassembly of check_no_overread and re-checked
   against lib/A/Listing_prog.v (the cut's blob 7ed1529926bd; slot kinds: PCall / PHi / PW).
   THE CUTS (DERIVED offset: pc, what holds there):
     CN_INIT    608 0x81b64  CA5 start, all three copies made, the 3rd non-NULL (`lbu s10, -0x558(s8)`)
     CN_INIT3   792 0x81c1c  CA5 start, the 3rd copy NULL (`li a0, 1` before `sb a0, -0x558(s8)`)
     CN_READ1   748 0x81bf0  CA6 start: the three structs zeroed, s10 = the g_own_ran_out byte read at CN_INIT
     CN_PN1     780 0x81c10  parse_noting (r1, size, d1), return site CN_RET1 784 0x81c14
     CN_READ2   944 0x81cb4  CA7 start (`lbu a0, -0x558(s8)`), s10 = r1, s7 = rc1
     CN_PN2     992 0x81ce4  parse_noting (r2, size, d2), return site CN_RET2 996 0x81ce8
     CN_READ3  1000 0x81cec  CA8 start (`li s5, 1`), s9 = rc2
     CN_PN3    1040 0x81d14  parse_noting (r3, size, d3), return site CN_RET3 1044 0x81d18
     CN_CMP    1048 0x81d1c  CA9 start (`lbu a0, -0x558(s8)`), s4 = rc3
     CN_FREE   1060 0x81d28  CA10 start (`mv a0, s9`), s9 = d1, s5 = r
   The frame: s1 = (entry sp - 192) land -32 (the realigned sp; sp = s1 from CA1 on), s11 = F = the class-3 fake frame
   (`__asan_stack_malloc_3 (0x140)` at 0x81974; the real-stack fallback 0x81988-0x819a0 is REFUTED in CA0: the UAR cell
   holds 1 by AR_laws_x field alx_const, ARx_const_law (lib/Reusable/YCbqG.v), and the capacity rule gives a
   frame, brief :44-45), s2 = F's shadow
   address, s8 = the auipc hi of g_own_ran_out (atom A_HI 9; A_alias_hints: A_HI 9 - 1368 = A_OBJ 13). The structs:
   d1 = F + 32, d2 = F + 128, d3 = F + 224 (56 bytes each; their shadow s2 + 4 .. + 10, + 16 .. + 22, + 28 .. + 34).
   The real-stack slots of the body (s1 + off): 24 r1, 32 the fake-frame pointer (F), 40 r2, 48 d2, 56 d1, 80 F.
   The copies r1 / r2 / r3 come from __wrap_malloc (a RUNTIME block, not the ledger: the text keeps Lam' ~ Lam).
   THE FORM (rulings 12:18Z-12:31Z): every segment is generic in the memory invariant P (srr_inv_laws; srr_inv_call
   across a call; srr_inv_mn where the callee asks memnorm at entry) and FORWARD (the internal file lane-102.md :29-30): it ends in
   the exit cut(s) it reaches, cn_ex_* below, `/\ P (ms_mem (cfg_ms c'))`; the segments compose by SRr_bind, and the
   function exit is cn_ex_ret (CA11's).
   g_own_ran_out / g_most: prh_glob carries both cells, so every cut's ledger takes `(ci_most D) own` at the own value
   the cut holds (0 at poison / copy1, the copies' own at copy2 / copy3, own0 at init / read1 / read2, an existential
   own at init3, 0 at read3 / cmp / pn1-3, ownl at free); prh_ledger_own / prh_ledger_most project the cells.
   THE ROOM POSITION (the POST-IMPLICATION form of the cut's texts, first bound at f97c): the text has NO entry
   position and NO run premise. Its post binds the readings' grants o1 o2 o0 (under own' = 0, CNO-COPY), the exact
   live set after (PresetReqAt.hlive_from over ck_cno_evs) and, for ANY run position with iface_room_pos at the
   entry state and prh_run_at over ck_cno_evs, the position after them. So every cut carries cn_prog D E S: the live
   set at S is hlive_from of the entry's over E, and the same implication over E, where E is the run events made
   since the entry (the granted copies' HMal, then the readings made, each parse_evs at its grant o). The readings'
   grants o1 o2 o0 are the LAST parameters of the cuts after them; cn_rd ties each struct to its reading's model
   outcome. The pieces and their spelling are the B' twin's (Cno102B_Base.v edf7c32cd661, cnb_ for cn_).
   THE WILD BUDGET (the cut's text: wild_room .. [] 6 at entry, the post under fpostFbm .. (wbudget [] 6)): the three
   parse_noting texts each add at most 2 fresh wild traces (their cursor frees). So cn_J is the journal AT A BUDGET wk
   (exists WS, ajournal_xw .. WS /\ wbudget [] wk WS) and cn_base takes wk LAST; each cut passes its spent budget as a
   constant (0 up to the first reading, 2 / 4 after one / two reading positions, 6 from the compare on). A reading's
   wild_room [] 2 comes from cn_pre's by YCbqGwild.ajournal_xw_room and wild_room_le; the next cut's WS is the old ++
   the reading's, by YCbqGwild.wbudget_app.
   K0-CNO-COPY (now the text's own conclusion: at a consumer run no copy was refused): cn_cdead D, the refusal's
   exclusion over the entry state, proved where a copy's malloc returned NULL (Cno102A_E2.v e2_cdead, by PRH_Refute.prh_refute_window) and carried
   by every cut that may hold a refused copy (`own <> 0 -> cn_cdead D`; outright at CN_INIT3).
   THE FREE-ORDER TIE (tparse_noting_specX's Some arm under K0-CFHEAD-16): cn_fo D W mem Lam o d st, made by each
   reading and carried to CN_FREE (by PRH_PjOrder.pj_foR_frame), read by CA10's pj_free calls: the former state premise
   K0-PJF-TIE is CLOSED. cn_pre is read BY NAME (cn_pre_* below).
   SM (the kit's next batch, lead 19:4xZ): the reader texts will state their events over the caller's run sm, not
   ReaderRes.jr_strtod. The pieces here are stated over jr_strtod as the cut's texts are (cn_pe, cn_ro, cn_fevs, cn_ranz,
   cn_rd, cn_pre, cn_Q); when the batch lands they take the run's sm, with `sm = ReaderRes.jr_strtod` as ONE premise
   where the instance is needed.
   cn_pre and the function exit cn_ex_ret are the text's premises and full post (RowsCpy on CA0-CA4, h-decbox-a14 on
   the top; CA10 / CA11 in Cno102A_F*.v build on this interface).
   Numerals: offsets above (DERIVED); 192 / 32 / 56 / 128 / 224 / 24 / 40 / 48 / 80 / 1368 (LENGTH: frame, struct and
   slot offsets, the lo12 of the hi/lo pair); 3 (the frame class); 16 (the padded copy's tail); 2 ^ 64 (LENGTH: the
   word range, as the cf layer's RELRO row spells it); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00cf YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun
  PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the cut offsets: DERIVED byte offsets inside check_no_overread ---- *)
(* cno's slot in the listing: DERIVED, = A_prog_slot AS_check_no_overread of lib/A/PAImg_prog.v (the cut's blob 505a51ff7d08)
   (A_entry_check_no_overread: sigma 0x81904, slot 201). PAImg_prog.v is NOT Required: its certificate checks the #102
   image's bytes, which the cb base f65cfdd5cac0 does not carry (CawA102's Caw102A_Base.v :9-12, same reason); the
   image fact cni_entry below ties the slot to pa_sigma *)
Definition CN_SLOT : nat := 201.
Definition CN_OFF : Z := 4 * Z.of_nat CN_SLOT.
Definition CN_INIT : Z := 608.
Definition CN_INIT3 : Z := 792.
Definition CN_READ1 : Z := 748.
Definition CN_PN1 : Z := 780.
Definition CN_RET1 : Z := 784.
Definition CN_READ2 : Z := 944.
Definition CN_PN2 : Z := 992.
Definition CN_RET2 : Z := 996.
Definition CN_READ3 : Z := 1000.
Definition CN_PN3 : Z := 1040.
Definition CN_RET3 : Z := 1044.
Definition CN_CMP : Z := 1048.
Definition CN_FREE : Z := 1060.
(* LENGTH: the class of the fake frame (__asan_stack_malloc_3) and the struct / slot offsets *)
Definition CN_CID : Z := 3.
(* the listing's own tables (lib/A/PAImg_prog.v's, the same terms; Caw102A_Base.v's PL_caw_A): the
   engine's vm_compute needs a closed table *)
Definition A_prog_tpi_cno : ptree asym := ptree_of_list A_prog_listing.
Definition A_prog_tw_cno : ctable := Eval vm_compute in (tw_of 0 A_prog_listing).
Definition PL_cno_A : PAListing A_prog_listing :=
{| pl_tpi := A_prog_tpi_cno; pl_tpi_eq := eq_refl; pl_tw := A_prog_tw_cno; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

(* the configuration at a cut, at the float state the callees left (parse_noting reaches musl strtod) *)
Definition cn_cfg {segs : list Segment} (fxk : YK11.FPState) (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : config :=
  mkCfg (@YK11.mkst fxk regs (w64 pc) mem (YK11.seg_rom segs)) md.

(* a register snapshot: each named register holds the given value (H5RttDefs.v's rt_regsat form) *)
Definition cn_regsat (regs : bvmap 5 word) (l : list (bv 5 * Z)) : Prop :=
  Forall (fun p => getr regs (fst p) = w64 (snd p)) l.

(* ---- THE MALLOC LAW, a companion class over the same RL (lead's ruling (A) 16:52Z, on RowsCpy's counterexample:
   room_live_cf after a raw __wrap_malloc was UNPROVABLE from PrhRoomLive's two frame laws). It mirrors PRH_Base.v's
   PrhRoomFree (3004a98fe2d9 :306-311, unchanged in shape at Batch 2): the field is a Theorem Labs lane's RL_malloc_step shape (lib/Reusable/YGcfRoomLive.v
   db11c2a5eb11 :1422-1424, the leaves2 blob of that lane's tip b902bb657c5c), so a walk that crosses a raw malloc
   takes {RM : PrhRoomMalloc} beside {RL : PrhRoomLive}. INTENDED HOME: the kit's lib/A/PRH_Base.v beside PrhRoomFree (the
   lead asked a Theorem Labs lane to adopt it, 16:5xZ); until the lane decides it lives here, stated in exactly RL_malloc_step's shape so
   that the move is a citation. No generic malloc law exists elsewhere (h-rw-pre-7's padded B' fixes RL :=
   prh_room_live_a8 and cites RL_malloc_step directly). ---- *)
Class PrhRoomMalloc {cp : CfParams} {RL : PrhRoomLive} : Type := MkPrhRoomMalloc {
  RM_malloc : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}
    segs B ly S Hp W regs mem md ch Lsec L24 n tr trc r,
    YG0dcf.acall_pre_cf segs B ly S Hp W regs mem md ch -> YGcfRoomLive.rl_sec_ok Lsec S ->
    YGcfRoomLive.rl_b24_ok L24 S -> room_live_cf S -> YG00.apath (YG00cf.malloc_cf n tr S) trc r ->
    room_live_cf (snd r)
}.
(* THE INSTANCE at the real RL (prh_room_live_a8): a8's RL_malloc_step at this cp, by that lemma (room_live_cf of
   prh_room_live_a8 is YGcfRoomLive.room_live_cf by conversion); so the class is inhabited at the instance *)
Definition prh_room_malloc_a8 {cp : CfParams} : @PrhRoomMalloc cp (@prh_room_live_a8 cp) :=
  @MkPrhRoomMalloc cp (@prh_room_live_a8 cp) (fun _ _ _ => YGcfRoomLive.RL_malloc_step (cp := cp)).

Section cn. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
(* ---- THE IMAGE FACTS the walk reads of PA (and of the image's runtime symbols B), each proved at the instance by
   computation (PAImg_prog.v
   47eeb54e93be: A_prog_val, A_entry_check_no_overread; the object pin 13 = g_own_ran_out) ---- *)
Record cn_img : Prop := {
  cni_base : BASE = A_prog_base;
  cni_entry : SIGMA AS_check_no_overread = BASE + CN_OFF;
  cni_own : VAL (A_OBJ 13) = pi_g_own_ran_out;
  (* the program statics are writable data, not read-only bytes: what carries arodata_okP across a call by the
     journal (CawA102's WA4 finding, Caw102A_Base.v 3e9f97debfb cwi_pst_rw) *)
  cni_pst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  (* a program static is a SEGMENT byte (.bss / .data of a LOAD segment), so a load of it reads a value whatever the
     memory holds there (CnoA9's finding: the lbu of g_own_ran_out after a call; S1ImgA.v pst_img_b_A's form) *)
  cni_pst_seg : forall a, Exists (in_zr a) prh_pst -> seg_rom SEGS (Z_to_bv 64 a) <> None;
  (* the journal's PST_ok (YCbqG.v :259, YC80x.v ajournal_x_exec_mixed, YC1fPx.v paj_run_x_m): a store to a program
     static is a store to an image byte the runtime does not own (CnoA5's finding, the 3rd-NULL arm's `sb 1` to
     g_own_ran_out; S1ImgA.v pst_in_img_A / FuzzFree.v :389 pal_pst_ok's form) *)
  cni_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B);
  (* the hi / lo pair that addresses g_own_ran_out (`auipc s8` at slot 302, then `lbu / sb .., -0x558(s8)`, PW slots
     the certificate does not check): lib/A/Listing_prog.v's alias row (the cut's blob 7ed1529926bd), proved at the instance by
     PAImg_prog.v A_alias_hints_ok (CnoA9's finding) *)
  cni_hi9 : VAL (A_HI 9) - 1368 = VAL (A_OBJ 13);
  (* the program statics are apart from errno: the runtime rows' image keep (YCbq.v acall_kept, through
     aj_free_at_x_ct_m) exempts errno, which api_env puts inside the image (CnoB102f's finding, lead 15:4xZ; B' twin
     cnbi_pst_errno). Closed by vm_compute at the instance. *)
  cni_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4);
  (* ---- THE cf LAYER'S RELRO ROWS (field round 3, lib/Reusable/YG0ncf.v relro_seg_t / errno_relro_t): what
     arodata_ok_cf asks of the image, and so what QMm_cf asks at every free / realloc call of the walk. The RELRO
     range of the cf image lies in ONE segment, errno's four bytes are apart from it, the range ends inside the
     address space, and it IS the listing's read-only range, so the walk's arodata_okP over pa_relro_lo /
     pa_relro_hi is a statement about the layer's range. Discharged at the instance as the other fields are. ---- *)
  cni_relro_seg : YG0ncf.relro_seg_t SEGS;
  cni_errno_relro : YG0ncf.errno_relro_t B;
  cni_relro_top : cf_relro_hi <= 2 ^ 64;
  cni_relro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA;
  cni_ro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS
}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation STK := STK_check_no_overread.

Definition cn_pc (off : Z) : Z := BASE + CN_OFF + off.

(* ---- THE ENTRY DATA: every variable the text binds, and the position __asan_stack_malloc_3 returned (the cut's text
   binds no run and no room position) ---- *)
Record cn_in : Type := mkCnIn {
  ci_ly : alayout; ci_S : astate; ci_Hp : list Z; ci_W : world SEGS;
  ci_regs : bvmap 5 word; ci_mem : word -> option byte; ci_md : Model; ci_ch : list (Z * Z * Z);
  ci_data : Z; ci_x : list Z; ci_Lam : list (Z * Z); ci_peak : Z; ci_cnt : Z; ci_ran : Z; ci_most : Z;
  ci_fpos : Z
}.

Definition cn_size (D : cn_in) : Z := Z.of_nat (length (ci_x D)).
Definition cn_sp0 (D : cn_in) : Z := spZ (ci_regs D).
(* the realigned body sp (`addi sp, sp, -192 .. andi sp, sp, -32; mv s1, sp`, 0x81904 / 0x81944 / 0x81948) *)
Definition cn_S1 (D : cn_in) : Z := Z.land (cn_sp0 D - 192) (-32).
(* the fake frame, at the entry layout (layout_le keeps ly_F, YG0f.v :65-70) *)
Definition cn_F (D : cn_in) : Z := frame_addr (ci_ly D) CN_CID (ci_fpos D).
Definition cn_d1 (D : cn_in) : Z := cn_F D + 32.
Definition cn_d2 (D : cn_in) : Z := cn_F D + 128.
Definition cn_d3 (D : cn_in) : Z := cn_F D + 224.

(* ---- THE HULL STAGES (route (b)): the all-granted event list the text's hull premise is stated over
   (PRH_FnCheck.v tcheck_no_overread, `PresetHullBudget.hull_budget S (ck_cno_evs .. x None None None)`), and
   one NAMED SUFFIX per stage of the walk: the part of that list still to be paid after the stage's calls. No
   reading runs out at the grant None (PresetRun.ranout .. None is false), so each suffix is the literal suffix
   of the all-granted list and every split below holds by reflexivity. A cut at a stage carries ONE plain
   conjunct `PresetHullBudget.hull_budget S (cn_hrest_<stage> (ci_x D))` over its OWN astate, LAST in the cut; the
   conjunct is not inside a journal, so it is the same in X and XR. ---- *)
Definition cn_hev_all (x : list Z) : list PresetReqAt.hev := ck_cno_evs ReaderRes.jr_strtod x None None None.
(* the pieces: one padded copy's malloc, the three copies' free *)
Definition cn_hmal (x : list Z) : PresetReqAt.hev :=
  PresetReqAt.HMal (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD).
Definition cn_hF3 (x : list Z) : list PresetReqAt.hev :=
  repeat (PresetReqAt.HFr (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD)) 3.
(* the stages: cpy1 / cpy2 after one / two of the three padded copies, copies after all three, rd1 / rd2 / rd0
   after each parse_noting, pf1 / pf2 / pf0 after each pj_free, and the three copies' free last *)
Definition cn_hrest_copies (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_cpy2 (x : list Z) : list PresetReqAt.hev := cn_hmal x :: cn_hrest_copies x.
Definition cn_hrest_cpy1 (x : list Z) : list PresetReqAt.hev := cn_hmal x :: cn_hrest_cpy2 x.
Definition cn_hrest_rd1 (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_rd2 (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_rd0 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_pf1 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_pf2 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hF3 x.
Definition cn_hrest_pf0 (x : list Z) : list PresetReqAt.hev := cn_hF3 x.
(* the split each stage's payment needs: what that stage's calls pay, then the suffix the next cut carries *)
Lemma cn_hrest_cpy1_split : forall x, cn_hev_all x = cn_hmal x :: cn_hrest_cpy1 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_cpy2_split : forall x, cn_hrest_cpy1 x = cn_hmal x :: cn_hrest_cpy2 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_copies_split : forall x, cn_hrest_cpy2 x = cn_hmal x :: cn_hrest_copies x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_rd1_split : forall x,
  cn_hrest_copies x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cn_hrest_rd1 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_rd2_split : forall x,
  cn_hrest_rd1 x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cn_hrest_rd2 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_rd0_split : forall x,
  cn_hrest_rd2 x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cn_hrest_rd0 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_pf1_split : forall x,
  cn_hrest_rd0 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hrest_pf1 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_pf2_split : forall x,
  cn_hrest_pf1 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hrest_pf2 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_pf0_split : forall x,
  cn_hrest_pf2 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cn_hrest_pf0 x.
Proof. intros x. reflexivity. Qed.
Lemma cn_hrest_frees_split : forall x, cn_hrest_pf0 x = cn_hF3 x.
Proof. intros x. reflexivity. Qed.
(* paying ONE padded copy out of a stage budget: the copy's own one-element budget (what the padded call's premise
   asks, its request spelled `+ 16`), and the rest of the stage's budget after the copy's use *)
Lemma cn_hpay_copy : forall S x rest,
  PresetHullBudget.hull_budget S (cn_hmal x :: rest) ->
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (Z.of_nat (length x) + 16)] /\
  (forall S', PresetHullBudget.hull_used S S' [cn_hmal x] -> PresetHullBudget.hull_budget S' rest).
Proof.
intros S x rest H.
assert (E : PresetReqAt.HMal (Z.of_nat (length x) + 16) = cn_hmal x)
  by (unfold cn_hmal, PresetReqAt.FUZZ_PAD; reflexivity).
split.
- rewrite E. apply (PresetHullBudget.hull_budget_weaken S [cn_hmal x] (cn_hmal x :: rest) H).
  + change (cn_hmal x :: rest) with ([cn_hmal x] ++ rest). rewrite PresetSecTotal.nsec_app. lia.
  + change (cn_hmal x :: rest) with ([cn_hmal x] ++ rest). rewrite PresetSecTotal.tsec_app.
    pose proof (PresetSecTotal.tsec_nn rest). lia.
- intros S' U. exact (PresetHullBudget.hull_budget_app S S' [cn_hmal x] rest H U).
Qed.

(* ---- tcheck_no_overread_specX's premises at one record (PRH_FnCheck.v c40cf3fdcd2a :738-777, the kit cut
   7cdbb61b5fa0), verbatim: no run-word list DW (K0-DW-SPLIT, prh_univ_closure CTX0); the wild-trace room for the three
   readings (prh_wk F_check_no_overread = 6); the room counts position-free (PresetRun.pkR along the all-granted
   events) ---- *)
Definition cn_pre (CTX0 : list (list Z)) (D : cn_in) : Prop :=
  let size := cn_size D in
  fpre B ARx STK (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_regs D) (ci_mem D) (ci_md D) (ci_ch D) /\
  YAkMemnorm.memnorm SEGS (ci_mem D) /\
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_check_no_overread (raZ (ci_regs D) :: spine (ci_ch D)) /\
  getr (ci_regs D) 10 = w64 (ci_data D) /\ getr (ci_regs D) 11 = w64 size /\
  size <= 3 * 2 ^ 20 /\
  src_rd (ci_W D) (ci_mem D) (ci_data D) (ci_x D) /\
  (0 < size -> PRH_FnReader.prhReader_home B (ci_ly D) (ci_S D) (ci_Hp D) (ci_Lam D) (ci_data D) size) /\
  prh_ledger B (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
    (ci_most D) 0 /\
  ci_cnt D < 2 ^ 62 - 2 ^ 30 /\
  ci_ran D = 0 /\
  PRH_FnPj.RQ_pj_parse (ci_x D) <= ci_most D /\
  blocks_bytes (ci_S D) + LIVE_check_no_overread (ci_x D) <= LIVE_MAX /\
  size + 16 < cf_malloc_max /\ PRH_FnPj.RQ_pj_parse (ci_x D) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (ci_S D))) <= ck_FRAMES_CAP - FR_check_no_overread /\
  room_live_cf (ci_S D) /\ ck_frm0 (fx := fx) /\
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot (ci_S D)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None)) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None)) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* the text's hull premise (PRH_FnCheck.v tcheck_no_overread): the whole call's allocator-hull budget at the
     entry state, which each cut pays down one stage at a time (cn_hrest_<stage> above) *)
  PresetHullBudget.hull_budget (ci_S D) (cn_hev_all (ci_x D)).

(* ---- cn_pre BY NAME: one projection per conjunct, in the text's order (a consumer cites these, never a positional
   pattern over cn_pre; the rebind brief's rule) ---- *)
Section pre_proj.
Variable CTX0 : list (list Z).
Variable D : cn_in.
Hypothesis HP : cn_pre CTX0 D.
Lemma cn_pre_fpre : fpre B ARx STK (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_regs D) (ci_mem D) (ci_md D) (ci_ch D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (H & _). exact H. Qed.
Lemma cn_pre_mn : YAkMemnorm.memnorm SEGS (ci_mem D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & H & _). exact H. Qed.
Lemma cn_pre_univ : prh_univ_closure B CTX0.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & H & _). exact H. Qed.
Lemma cn_pre_ctx : prh_ctx CTX0 F_check_no_overread (raZ (ci_regs D) :: spine (ci_ch D)).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_r10 : getr (ci_regs D) 10 = w64 (ci_data D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_r11 : getr (ci_regs D) 11 = w64 (cn_size D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_size : cn_size D <= 3 * 2 ^ 20.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_src : src_rd (ci_W D) (ci_mem D) (ci_data D) (ci_x D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_home : 0 < cn_size D -> PRH_FnReader.prhReader_home B (ci_ly D) (ci_S D) (ci_Hp D) (ci_Lam D) (ci_data D) (cn_size D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_ledger : prh_ledger B (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
    (ci_most D) 0.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_cnt : ci_cnt D < 2 ^ 62 - 2 ^ 30.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_ran : ci_ran D = 0.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_most : PRH_FnPj.RQ_pj_parse (ci_x D) <= ci_most D.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_live : blocks_bytes (ci_S D) + LIVE_check_no_overread (ci_x D) <= LIVE_MAX.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_max16 : cn_size D + 16 < cf_malloc_max.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_maxpj : PRH_FnPj.RQ_pj_parse (ci_x D) + cf_head < cf_malloc_max.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_frames : Z.of_nat (length (frames (ci_S D))) <= ck_FRAMES_CAP - FR_check_no_overread.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_room : room_live_cf (ci_S D).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_frm0 : ck_frm0 (fx := fx).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_wild : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot (ci_S D)).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_pksec : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None)) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_pk24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None)) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma cn_pre_hull : PresetHullBudget.hull_budget (ci_S D) (cn_hev_all (ci_x D)).
Proof. pose proof HP as HP'. unfold cn_pre in HP'. cbv zeta in HP'. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
End pre_proj.

(* ---- the text's post body at one record (PRH_FnCheck.v c40cf3fdcd2a :787-823), verbatim; the post ---- *)
Definition cn_Q (D : cn_in) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) ->
  Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
    Permutation Lam' (ci_Lam D) /\ Permutation (ablocks B ly' S') (ablocks B (ci_ly D) (ci_S D)) /\
    ci_peak D <= peak' /\ ci_cnt D <= cnt' <= ci_cnt D + 3 * ck_ncalls (ci_x D) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' (ci_most D) own' /\
    bytes_at W' mem' (ci_data D) (ci_x D) /\
    exists r, getr regs' 10 = w64 r /\
      ((r = 1 /\ (own' = 1 \/ ran' = 1)) \/ (r = 0 /\ own' = 0 /\ ran' = 0)) /\
      (* K0-CNO-COPY, now the text's own conclusion: at a run position whose next events are the three copies, each
         a consumer event, no copy was refused *)
      (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist (ci_S D) ->
         PRH_Base.prh_run_at sm x0 os i (ck_cno_copies (ci_x D)) ->
         PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies (ci_x D))) -> own' = 0) /\
      (own' = 0 -> exists o1 o2 o0 : option nat,
         r = (if ck_cno_ranout ReaderRes.jr_strtod (ci_x D) o1 o2 o0 then 1 else 0) /\
         Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
           (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
              (ck_cno_evs ReaderRes.jr_strtod (ci_x D) o1 o2 o0)) /\
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x0 os i H0 hist (ci_S D) ->
            PRH_Base.prh_run_at sm x0 os i (ck_cno_evs ReaderRes.jr_strtod (ci_x D) o1 o2 o0) ->
            exists hist', PresetRoomPos.iface_room_pos sm x0 os
              (i + length (ck_cno_evs ReaderRes.jr_strtod (ci_x D) o1 o2 o0))%nat H0 hist' S')).
Definition cn_post (D : cn_in) : world SEGS -> config -> Prop :=
  fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread)) STK [] (ci_regs D) (ci_ly D) (ci_S D)
    (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) (cn_Q D).
(* the post and the exit over a world relation R, through the kit's R families (PRH_Base.v): fpostFbm / fpostFb are
   AFTER-FREE-ONLY, so the kit owner states them IN PLACE at wle' SEGS YGcfRehidePost.RZ_cf and the guard below is the wle'
   one (the kit's naming: X_R_wle when the plain form is the wle instance, X_R_wle' when it is the wle' instance) *)
Definition cn_postR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop :=
  fpostFbmR B ARx SK R (YCbqGwild.wbudget [] (prh_wk F_check_no_overread)) STK [] (ci_regs D) (ci_ly D) (ci_S D)
    (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) (cn_Q D).
Lemma cn_post_R_wle' : forall D,
  cn_post D = cn_postR (wle' SEGS YGcfRehidePost.RZ_cf) D.
Proof. reflexivity. Qed.
(* THE FUNCTION EXIT the segments reach (CA11's exit): the text's FULL post body cn_Q at the text's wild budget
   (YCbqGwild.wbudget [] 6 of the fresh wild traces the three readings add). cn_post is the same body under fpostFbm
   (the memnorm keep, given by P := cn_mn). *)
Definition cn_ex_ret (D : cn_in) : world SEGS -> config -> Prop :=
  fpostFb B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread)) STK [] (ci_regs D) (ci_ly D) (ci_S D)
    (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) (cn_Q D).
Definition cn_ex_retR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop :=
  fpostFbR B ARx SK R (YCbqGwild.wbudget [] (prh_wk F_check_no_overread)) STK [] (ci_regs D) (ci_ly D) (ci_S D)
    (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) (cn_Q D).
Lemma cn_ex_ret_R_wle' : forall D,
  cn_ex_ret D = cn_ex_retR (wle' SEGS YGcfRehidePost.RZ_cf) D.
Proof. reflexivity. Qed.

(* ---- the memory invariant at the top: memnorm of the entry memory gives memnorm at m ---- *)
Definition cn_mn (D : cn_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm SEGS (ci_mem D) -> YAkMemnorm.memnorm SEGS m.
Lemma cn_mn_laws : forall D, srr_inv_laws SEGS (cn_mn D).
Proof. intros D. exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (ci_mem D) (srr_inv_laws_memnorm_k SEGS)). Qed.
Lemma cn_mn_call : forall D, srr_inv_call SEGS (cn_mn D).
Proof. intros D. exact (srr_inv_call_imp SEGS (ci_mem D)). Qed.
Lemma cn_mn_mn : forall CTX0 D, cn_pre CTX0 D -> srr_inv_mn SEGS (cn_mn D).
Proof.
intros CTX0 D H. unfold cn_pre in H. cbv zeta in H. destruct H as (_ & HMN & _).
exact (srr_inv_mn_imp SEGS (ci_mem D) HMN).
Qed.
Lemma cn_mn_entry : forall D, cn_mn D (ci_mem D).
Proof. intros D H. exact H. Qed.

(* ---- what every cut from CA5 on carries ---- *)
(* the journal from entry, the function's own class-3 frame in `own`, AT A WILD BUDGET (the kit cut's journal,
   YCbqG.ajournal_xw): the fresh wild traces WS it added are at most wk, the budget the cut has spent (a constant per
   cut: 0 before the first reading, 2 / 4 after one / two reading positions, 6 from the compare on; the three readings'
   parse_noting texts take 2 each, prh_wk F_parse_noting); ajournal_x is its WS = [] instance *)
Definition cn_J (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (k : Z) (wk : nat) : Prop :=
  exists WS, ajournal_xw (SK := SK) SEGS B prh_pst ARx STK (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D)
    (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
(* the journal over a world relation R (YCbqG.ajournal_xwR): the cuts after a free or realloc carry it at the
   walk's relation; cn_J keeps its body (proofs unfold it) and cn_J_R_wle ties the copy *)
Definition cn_JR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (k : Z) (wk : nat) : Prop :=
  exists WS, ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D)
    (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
Lemma cn_J_R_wle : forall D ly S Hp W mem md k wk,
  cn_J D ly S Hp W mem md k wk = cn_JR (@wle SEGS) D ly S Hp W mem md k wk.
Proof. reflexivity. Qed.
(* THE THIRTEEN SAVED WORDS at entry sp - 192 + off (0x8190c-0x8193c): ra 184, s0 176, s1 168, s2 160 .. s11 88 *)
Definition cn_saved (D : cn_in) (W : world SEGS) (mem : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H W) mem) (cn_sp0 D - 192 + fst p) = Some (bv_unsigned (getr (ci_regs D) (snd p))))
    [(184, 1%bv); (176, 8%bv); (168, 9%bv); (160, 18%bv); (152, 19%bv); (144, 20%bv); (136, 21%bv);
     (128, 22%bv); (120, 23%bv); (112, 24%bv); (104, 25%bv); (96, 26%bv); (88, 27%bv)].
(* the frame: live on top of the entry's frames, its flag word, its bytes and its shadow present *)
Definition cn_frame (D : cn_in) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) : Prop :=
  frames S = (CN_CID, ci_fpos D) :: frames (ci_S D) /\ ~ In (CN_CID, ci_fpos D) (frames (ci_S D)) /\
  rdword (aview SEGS (w_H W) mem) (cn_F D + fs_frame_bytes CN_CID - 8) = Some (flag_addr ly CN_CID (ci_fpos D)) /\
  (forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID -> apresent (w_H W) mem a) /\
  (forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + fs_frame_bytes CN_CID / 8 -> apresent (w_H W) mem a).
(* the body's real-stack slots at s1: 24 r1, 32 the fake-frame pointer, 40 r2, 48 d2, 56 d1, 80 F *)
Definition cn_slots (D : cn_in) (W : world SEGS) (mem : word -> option byte) (r1 r2 : Z) : Prop :=
  Forall (fun p : Z * Z => rdword (aview SEGS (w_H W) mem) (cn_S1 D + fst p) = Some (snd p))
    [(24, r1); (32, cn_F D); (40, r2); (48, cn_d2 D); (56, cn_d1 D); (80, cn_F D)].
(* the registers every cut from CA5 on holds: sp = s1, s0 = the entry sp, s2 = F's shadow, s11 = F, gp, tp *)
Definition cn_core (D : cn_in) : list (bv 5 * Z) :=
  [(2%bv, cn_S1 D); (8%bv, cn_sp0 D); (9%bv, cn_S1 D); (18%bv, shadow_addr (cn_F D)); (27%bv, cn_F D)].
(* s8: the auipc hi of g_own_ran_out (Listing_prog.v slot 302 `PHi 24 9`) *)
Definition cn_s8 : bv 5 * Z := (24%bv, VAL (A_HI 9)).
(* cn_base over a world relation R: its journal is cn_JR R; cn_base is the instance at wle. Every cut below is
   stated the same way: X R is the cut over R, X its wle instance (or, where proofs unfold X, a copy of X's body
   tied by X_R_wle) *)
Definition cn_baseR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (wk : nat) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  cn_JR R D ly S Hp W mem md k wk /\ cn_frame D ly S W mem /\ cn_saved D W mem /\
  getr regs 3 = getr (ci_regs D) 3 /\ getr regs 4 = getr (ci_regs D) 4 /\
  (* the read-only view, fpre's second conjunct at every call *)
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Definition cn_base (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (wk : nat) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  cn_J D ly S Hp W mem md k wk /\ cn_frame D ly S W mem /\ cn_saved D W mem /\
  getr regs 3 = getr (ci_regs D) 3 /\ getr regs 4 = getr (ci_regs D) 4 /\
  (* the read-only view, fpre's second conjunct at every call *)
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Lemma cn_base_R_wle : forall D fxk ly S Hp W regs mem md k wk,
  cn_base D fxk ly S Hp W regs mem md k wk = cn_baseR (@wle SEGS) D fxk ly S Hp W regs mem md k wk.
Proof. reflexivity. Qed.

(* ---- THE WILD BUDGET's facts the segments use: the empty budget from a plain journal, a larger budget, and a
   reading's room (a Theorem Labs lane's ec_room_at: cn_pre's wild_room [] 6 across the journal so far) ---- *)
Lemma cn_J_of_x : forall D ly S Hp W mem md k wk,
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D)
    (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k -> cn_J D ly S Hp W mem md k wk.
Proof.
intros D ly S Hp W mem md k wk HJ. exists []. split; [exact HJ|].
unfold YCbqGwild.wbudget. rewrite YCbqGwild.wfresh_nil_set. apply Nat.le_0_l.
Qed.
Lemma cn_J_mono : forall D ly S Hp W mem md k wk wk', (wk <= wk')%nat ->
  cn_J D ly S Hp W mem md k wk -> cn_J D ly S Hp W mem md k wk'.
Proof.
intros D ly S Hp W mem md k wk wk' Hle (WS & HJ & HB). exists WS. split; [exact HJ|].
unfold YCbqGwild.wbudget in *. lia.
Qed.
Lemma cn_base_mono : forall D fxk ly S Hp W regs mem md k wk wk', (wk <= wk')%nat ->
  cn_base D fxk ly S Hp W regs mem md k wk -> cn_base D fxk ly S Hp W regs mem md k wk'.
Proof.
intros D fxk ly S Hp W regs mem md k wk wk' Hle (H1 & H2 & HJ & H3).
exact (conj H1 (conj H2 (conj (cn_J_mono D ly S Hp W mem md k wk wk' Hle HJ) H3))).
Qed.
Lemma cn_room_pn : forall CTX0 D ly S Hp W mem md k wk, cn_pre CTX0 D -> cn_J D ly S Hp W mem md k wk ->
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S).
Proof.
intros CTX0 D ly S Hp W mem md k wk HP (WS & HJ & HB) Hle.
pose proof (cn_pre_wild CTX0 D HP) as Hr.
unfold YCbqGwild.wbudget in HB.
assert (Hk : (YCbqGwild.wfresh [] WS <= prh_wk F_check_no_overread)%nat) by lia.
pose proof (YCbqGwild.ajournal_xw_room (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hr Hk)
  as Hr'.
eapply YCbqGwild.wild_room_le; [|exact Hr']. lia.
Qed.

(* ---- THE SAME FACTS OVER A WORLD RELATION R: the budget facts at R (suffix _wk), the room of a reading, and
   THE MONO over the relation itself ---- *)
Lemma cn_JR_of_x : forall R D ly S Hp W mem md k wk,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D)
    (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k -> cn_JR R D ly S Hp W mem md k wk.
Proof.
intros R D ly S Hp W mem md k wk HJ. exists []. split; [exact HJ|].
unfold YCbqGwild.wbudget. rewrite YCbqGwild.wfresh_nil_set. apply Nat.le_0_l.
Qed.
Lemma cn_JR_mono_wk : forall R D ly S Hp W mem md k wk wk', (wk <= wk')%nat ->
  cn_JR R D ly S Hp W mem md k wk -> cn_JR R D ly S Hp W mem md k wk'.
Proof.
intros R D ly S Hp W mem md k wk wk' Hle (WS & HJ & HB). exists WS. split; [exact HJ|].
unfold YCbqGwild.wbudget in *. lia.
Qed.
Lemma cn_baseR_mono_wk : forall R D fxk ly S Hp W regs mem md k wk wk', (wk <= wk')%nat ->
  cn_baseR R D fxk ly S Hp W regs mem md k wk -> cn_baseR R D fxk ly S Hp W regs mem md k wk'.
Proof.
intros R D fxk ly S Hp W regs mem md k wk wk' Hle (H1 & H2 & HJ & H3).
exact (conj H1 (conj H2 (conj (cn_JR_mono_wk R D ly S Hp W mem md k wk wk' Hle HJ) H3))).
Qed.
(* ---- THE MONO OVER THE WORLD RELATION, the lift a walk uses at the boundary: a cut proved BEFORE the free
   carries its journal at wle, and the cut AFTER it wants the same cut at the walk's relation. Every XR whose only
   R-carrying part is the journal has one, by YCbqG.ajournal_xwR_mono at the base and by chaining it upwards; at
   R1 := wle, R2 := wle' SEGS RZ_cf the premise is YA0nH.wle_wle'. ---- *)
Lemma cn_JR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D ly S Hp W mem md k wk, cn_JR R1 D ly S Hp W mem md k wk -> cn_JR R2 D ly S Hp W mem md k wk.
Proof.
intros R1 R2 H12 D ly S Hp W mem md k wk (WS & HJ & HB). exists WS. split; [|exact HB].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.
Lemma cn_baseR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k wk,
  cn_baseR R1 D fxk ly S Hp W regs mem md k wk -> cn_baseR R2 D fxk ly S Hp W regs mem md k wk.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k wk (H1 & H2 & HJ & H3).
split; [exact H1|]. split; [exact H2|]. split; [|exact H3].
apply (cn_JR_mono R1 R2 H12). exact HJ.
Qed.
Lemma cn_room_pnR : forall R CTX0 D ly S Hp W mem md k wk, cn_pre CTX0 D -> cn_JR R D ly S Hp W mem md k wk ->
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S).
Proof.
intros R CTX0 D ly S Hp W mem md k wk HP (WS & HJ & HB) Hle.
pose proof (cn_pre_wild CTX0 D HP) as Hr.
unfold YCbqGwild.wbudget in HB.
assert (Hk : (YCbqGwild.wfresh [] WS <= prh_wk F_check_no_overread)%nat) by lia.
pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
  Hr Hk) as Hr'.
eapply YCbqGwild.wild_room_le; [|exact Hr']. lia.
Qed.

(* a padded copy: NULL, or a live RUNTIME block of size + 16 (not a harness block) whose first size bytes are x *)
Definition cn_copy (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (r : Z) : Prop :=
  r = 0 \/ (In (r, cn_size D + 16) (ablocks B ly S) /\ ~ In r Hp /\ src_rd W mem r (ci_x D)).
Definition cn_cblk (D : cn_in) (r : Z) : list (Z * Z) := if r =? 0 then [] else [(r, cn_size D + 16)].
Definition cn_cblks (D : cn_in) (r1 r2 r3 : Z) : list (Z * Z) := cn_cblk D r1 ++ cn_cblk D r2 ++ cn_cblk D r3.

(* a struct's state: a tree the reading built (its blocks in Lam), or the zero struct (`= empty`, the memset) *)
Definition cn_st : Type := option (PjTree.jv * list (Z * Z)).
Definition cn_Dof (st : cn_st) : list (Z * Z) := match st with Some (_, Dd) => Dd | None => [] end.
Definition cn_doc (W : world SEGS) (mem : word -> option byte) (Lam : list (Z * Z)) (d : Z) (st : cn_st) : Prop :=
  match st with
  | Some (t, Dd) => pj_nodeR SEGS (rdW W mem) (prh_lin Lam) d t Dd /\ (PjTree.depth t <= PjGrammar.MAXD)%nat
  | None => pj_zeroR SEGS (rdW W mem) d
  end.
(* a struct's 56 bytes addressable and their shadow hull visible (CA5's unpoison; what parse_noting, same and pj_free
   read of the slot) *)
Definition cn_open (W : world SEGS) (mem : word -> option byte) (d : Z) : Prop :=
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF d 56 /\ shadow_hull_vis (aview SEGS (w_H W) mem) d 56.
(* WHAT A READING WITH NO RAN-OUT GIVES (the compare's refutation rests on it): while g_ran_out is still 0, a reading
   done is the grammar's reading of x; a reading skipped by the guard has g_ran_out = 1. ran is monotone (prh_oks:
   ran' = ran \/ ran' = 1; the accessors keep it), so the CURRENT ran is the premise. *)
Definition cn_res (D : cn_in) (ran rc : Z) (st : cn_st) : Prop :=
  ran = 0 ->
  match ck_read (ci_x D) with
  | Some t => rc = 0 /\ exists Dd, st = Some (t, Dd)
  | None => rc = -1 /\ st = None
  end.
(* ---- check_no_overread's RUN EVENTS, the pieces the cuts carry (the text's own list ck_cno_evs, PRH_FnCheck.v
   9ecd8eb167c6 :250-263, cut where each segment ends; cn_ck_cno_evs below is the equation). The B' twin's spelling
   (Cno102B_Base.v edf7c32cd661, cnb_ for cn_), name for name. ---- *)
(* the granted copies' __wrap_malloc (a refused copy makes no event) *)
Definition cn_cevs (D : cn_in) (r1 r2 r3 : Z) : list PresetReqAt.hev :=
  map (fun _ => PresetReqAt.HMal (cn_size D + PresetReqAt.FUZZ_PAD)) (cn_cblks D r1 r2 r3).
(* the copies made so far before CA5 (rs, in order; A' makes its three copies inline, one __wrap_malloc each) *)
Definition cn_cevsl (D : cn_in) (rs : list Z) : list PresetReqAt.hev :=
  map (fun _ => PresetReqAt.HMal (cn_size D + PresetReqAt.FUZZ_PAD)) (flat_map (cn_cblk D) rs).
(* the three copies granted, the text's C3 *)
Definition cn_C3 (D : cn_in) : list PresetReqAt.hev := repeat (PresetReqAt.HMal (cn_size D + PresetReqAt.FUZZ_PAD)) 3.
(* one reading's events under its grant o (pj_parse's reader events, then pj_free (out) on a refusal) *)
Definition cn_pe (D : cn_in) (o : option nat) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod (ci_x D) (PresetRun.okof o).
(* the reading under grant o RAN OUT (the model's ranout) *)
Definition cn_ro (D : cn_in) (o : option nat) : bool := PresetRun.ranout ReaderRes.jr_strtod (ci_x D) o.
(* the readings' events after one / two / three reading positions: a reading is skipped once one ran out *)
Definition cn_revs2 (D : cn_in) (o1 o2 : option nat) : list PresetReqAt.hev :=
  cn_pe D o1 ++ (if cn_ro D o1 then [] else cn_pe D o2).
Definition cn_revs3 (D : cn_in) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  cn_pe D o1 ++ (if cn_ro D o1 then [] else cn_pe D o2 ++ (if cn_ro D o2 then [] else cn_pe D o0)).
(* the frees' events (CA10): the accepted trees' pj_free, then the three copies' free *)
Definition cn_fevs (D : cn_in) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  (if cn_ro D o1 then []
   else if cn_ro D o2 then PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o1
   else PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o1 ++ PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o2 ++
        PresetRun.p1_tfree ReaderRes.jr_strtod (ci_x D) o0) ++
  repeat (PresetReqAt.HFr (cn_size D + PresetReqAt.FUZZ_PAD)) 3.
(* g_ran_out after the readings under these grants: 1 exactly when one ran out *)
Definition cn_ranz (D : cn_in) (o1 o2 o0 : option nat) : Z :=
  if ck_cno_ranout ReaderRes.jr_strtod (ci_x D) o1 o2 o0 then 1 else 0.
(* THE EQUATION: the pieces are the text's list *)
Lemma cn_ck_cno_evs : forall D o1 o2 o0,
  cn_C3 D ++ cn_revs3 D o1 o2 o0 ++ cn_fevs D o1 o2 o0 = ck_cno_evs ReaderRes.jr_strtod (ci_x D) o1 o2 o0.
Proof.
intros D o1 o2 o0. unfold cn_C3, cn_revs3, cn_fevs, cn_pe, cn_ro, ck_cno_evs, cn_size. cbv zeta.
destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) o1);
  [|destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) o2)];
  rewrite ?app_nil_r; repeat rewrite <- app_assoc; reflexivity.
Qed.
(* THE PROGRESS FACT a cut carries for the events E made since entry (the text's post-implication form): the live set
   is the entry's advanced by E, and for ANY run position at the entry state whose next events are E, the position
   after E is a position of this state *)
Definition cn_prog (D : cn_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D))) E) /\
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist (ci_S D) -> PRH_Base.prh_run_at sm x0 os i E ->
     exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E)%nat H0 hist' S).
(* a reading's struct against its model outcome at grant o: a filled struct holds the tree the model's reading at o
   accepts, a zeroed one is a reading the model refuses (what matches pj_free's event to p1_tfree o at CA10) *)
Definition cn_rd (D : cn_in) (o : option nat) (st : cn_st) : Prop :=
  match st with
  | Some (t, _) => fst (PjGrammar.jr_run ReaderRes.jr_strtod (ci_x D) (PresetRun.okof o)) = Some t
  | None => fst (PjGrammar.jr_run ReaderRes.jr_strtod (ci_x D) (PresetRun.okof o)) = None
  end.
(* the structs against the readings' grants (the B' twin's packers, Cno102B_Base.v 053287f9420d): a reading made
   matches its model outcome, a reading SKIPPED (one before it ran out) left the zero struct, so its pj_free makes no
   event *)
Definition cn_rds2 (D : cn_in) (o1 o2 : option nat) (st1 st2 : cn_st) : Prop :=
  cn_rd D o1 st1 /\ (if cn_ro D o1 then st2 = None else cn_rd D o2 st2).
Definition cn_rds3 (D : cn_in) (o1 o2 o0 : option nat) (st1 st2 st3 : cn_st) : Prop :=
  cn_rd D o1 st1 /\
  (if cn_ro D o1 then st2 = None /\ st3 = None
   else cn_rd D o2 st2 /\ (if cn_ro D o2 then st3 = None else cn_rd D o0 st3)).
(* K0-CNO-COPY's refused arm, DEAD under the run hypothesis (the text's conclusion at PRH_FnCheck.v c40cf3fdcd2a
   :801-804; caw_dead's shape): at any run position at the ENTRY state whose next events are the three copies, each a
   consumer event, no copy was refused. Proved where a copy's malloc returned NULL (Cno102A_E2.v e2_cdead, by
   PRH_Refute.prh_refute_window: the granted NULL path at the copy's own state, cn_prog over the copies before it), and
   carried, state-free, by every cut that may hold a refused copy (`own <> 0 -> cn_cdead D`), so CA11's exit derives
   own' = 0 at every consumer run. The B' twin's cnb_cdead. *)
Definition cn_cdead (D : cn_in) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (ci_S D) ->
    PRH_Base.prh_run_at sm x0 os i (ck_cno_copies (ci_x D)) ->
    PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies (ci_x D))) -> False.
(* THE FREE-ORDER TIE of an accepted reading's struct (tparse_noting_specX's Some arm, PRH_FnCheck.v c40cf3fdcd2a
   :718-720, under K0-CFHEAD-16): for every depth bound n >= depth t, pj_free's order list F of the struct's tree has the
   model's reader-side free list pj_frees at the reading's grant o as its sizes (+ cf_head), in order. Made by the
   reading (CA6-CA8's parse_noting step), carried to the free cut by PRH_PjOrder.pj_foR_frame, read by CA10's pj_free
   calls: this CLOSES the former state premise K0-PJF-TIE (cn_pjf_tie). The B' twin's cnb_fo. *)
Definition cn_fo (D : cn_in) (W : world SEGS) (mem : word -> option byte) (Lam : list (Z * Z)) (o : option nat)
  (d : Z) (st : cn_st) : Prop :=
  match st with
  | Some (t, Dd) => cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
      exists F, PRH_PjOrder.pj_foR SEGS (rdW W mem) (prh_lin Lam) n d Dd F /\
        map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (ci_x D)
  | None => True
  end.
(* NO count premise for the three copy calls: RM_malloc's live-set premises (rl_sec_ok / rl_b24_ok) at each copy
   call's OWN state come from cn_pre's two position-free peak counts (PresetRun.pkR over ck_cno_evs .. None None None
   from the entry's live set) and the cut's live set (cn_prog over the copies made so far), by PresetRun.pkR_app /
   pkR_prefix: a count at a prefix is below the peak. Each copy's __wrap_malloc runs at its cut's allocator state -
   only register steps lie between the cut and the call (A' twin listing: CN_COPY1 0x81a88 addi / mv, jal 0x81a90;
   CN_COPY2 0x81ad0 mv, jal 0x81ad4; CN_COPY3 0x81b18 addi x3 / mv, jal 0x81b28). *)

(* THE STATE FACTS after CA5 (structs open), nr readings done: copies, ledger (own: the g_own_ran_out byte the cut
   holds), counts, room, budget, the three structs and the blocks they hold *)
Definition cn_mid (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (Lam : list (Z * Z)) (peak cnt ran own : Z) (nr : nat) (r1 r2 r3 : Z) (st1 st2 st3 : cn_st) : Prop :=
  cn_copy D ly S Hp W mem r1 /\ cn_copy D ly S Hp W mem r2 /\ cn_copy D ly S Hp W mem r3 /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) own /\
  ci_peak D <= peak /\ ci_cnt D <= cnt <= ci_cnt D + Z.of_nat nr * ck_ncalls (ci_x D) /\
  room_live_cf S /\
  blocks_bytes S + Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  cn_open W mem (cn_d1 D) /\ cn_open W mem (cn_d2 D) /\ cn_open W mem (cn_d3 D) /\
  cn_doc W mem Lam (cn_d1 D) st1 /\ cn_doc W mem Lam (cn_d2 D) st2 /\ cn_doc W mem Lam (cn_d3 D) st3 /\
  Permutation Lam (cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3 ++ ci_Lam D) /\
  Permutation (ablocks B ly S)
    (cn_cblks D r1 r2 r3 ++ ck_hblks (cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3) ++ ablocks B (ci_ly D) (ci_S D)) /\
  (forall a k, In (a, k) (cn_Dof st1 ++ cn_Dof st2 ++ cn_Dof st3) ->
     ~ In (a - cf_head, k + cf_head) (ablocks B (ci_ly D) (ci_S D))).

(* ---- THE CUTS INSIDE CA0-CA4 (frozen 14:4xZ for the owner's hands; statements only). Offsets (DERIVED):
     CN_POISON 160 0x819a4  CA1 start: `sd a0, 0x20(s1)`, the fake frame F in a0 and s11, s2 = the shadow base
     CN_COPY1  388 0x81a88  CA2 start: `addi s3, s4, 0x10`, the frame poisoned, s2 = F's shadow, slots 32 / 80 = F
     CN_COPY2  460 0x81ad0  CA3 start: `mv a0, s3`, copy 1 made (r1 in s5) or its NULL noted
     CN_COPY3  532 0x81b18  CA4 start: `addi s9, s11, 0x20`, copy 2 made (slots 24 r1 / 40 r2) or noted
   ---- *)
Definition CN_POISON : Z := 160.
Definition CN_COPY1 : Z := 388.
Definition CN_COPY2 : Z := 460.
Definition CN_COPY3 : Z := 532.
(* some of the body's real-stack slots *)
Definition cn_slotsL (D : cn_in) (W : world SEGS) (mem : word -> option byte) (l : list (Z * Z)) : Prop :=
  Forall (fun p : Z * Z => rdword (aview SEGS (w_H W) mem) (cn_S1 D + fst p) = Some (snd p)) l.
(* the state facts before the structs exist (CA0-CA4): the copies made so far (rs, in order), the entry's ledger and
   heads (its own: the g_own_ran_out byte, 0 at entry, 1 once a copy was NULL; its most: the entry's), the blocks the
   copies added, the room, the budget for the copies still to come, and the g_own_ran_out byte *)
Definition cn_early (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (rs : list Z) (own : Z) : Prop :=
  Hp = ci_Hp D /\
  prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own /\
  Forall (cn_copy D ly S Hp W mem) rs /\
  Permutation (ablocks B ly S) (flat_map (cn_cblk D) rs ++ ablocks B (ci_ly D) (ci_S D)) /\
  room_live_cf S /\ cn_prog D (cn_cevsl D rs) S /\
  blocks_bytes S + Z.of_nat (3 - length rs) * (cn_size D + 16) + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  (own = 0 \/ own = 1) /\ val_mem SEGS (rdW W mem) (VAL (A_OBJ 13)) 1 own /\
  (own = 0 -> Forall (fun r => r <> 0) rs) /\
  (own <> 0 -> cn_cdead D).
(* CN_POISON (CA1 start): the class-3 fake frame taken (cn_base's cn_frame), a0 = s11 = F, s2 = SHADOW_OFF (loaded
   from __asan_shadow_memory_dynamic_address), s4 = size, s7 = data, sp = s1 *)
Definition cn_at_poisonR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs [(2%bv, cn_S1 D); (8%bv, cn_sp0 D); (9%bv, cn_S1 D); (10%bv, cn_F D); (18%bv, SHADOW_OFF);
                  (20%bv, cn_size D); (23%bv, ci_data D); (27%bv, cn_F D)] /\
  cn_early D ly S Hp W mem [] 0 /\
  PresetHullBudget.hull_budget S (cn_hev_all (ci_x D)).
Definition cn_at_poison (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs [(2%bv, cn_S1 D); (8%bv, cn_sp0 D); (9%bv, cn_S1 D); (10%bv, cn_F D); (18%bv, SHADOW_OFF);
                  (20%bv, cn_size D); (23%bv, ci_data D); (27%bv, cn_F D)] /\
  cn_early D ly S Hp W mem [] 0 /\
  PresetHullBudget.hull_budget S (cn_hev_all (ci_x D)).
Lemma cn_at_poison_R_wle : forall D fxk ly S Hp W regs mem md k,
  cn_at_poison D fxk ly S Hp W regs mem md k = cn_at_poisonR (@wle SEGS) D fxk ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* CN_COPY1 (CA2 start): the frame poisoned (header and redzones written; the structs' shadow bytes are present by
   cn_frame), s2 = F's shadow, slots 32 / 80 = F *)
Definition cn_at_copy1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [(20%bv, cn_size D); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(32, cn_F D); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [] 0 /\
  PresetHullBudget.hull_budget S (cn_hev_all (ci_x D)).
Definition cn_at_copy1 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [(20%bv, cn_size D); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(32, cn_F D); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [] 0 /\
  PresetHullBudget.hull_budget S (cn_hev_all (ci_x D)).
Lemma cn_at_copy1_R_wle : forall D fxk ly S Hp W regs mem md k,
  cn_at_copy1 D fxk ly S Hp W regs mem md k = cn_at_copy1R (@wle SEGS) D fxk ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* CN_COPY2 (CA3 start): copy 1 done, r1 in s5, s3 = size + 16, s8 the hi of g_own_ran_out *)
Definition cn_at_copy2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 own : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(32, cn_F D); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [r1] own /\
  PresetHullBudget.hull_budget S (cn_hrest_cpy1 (ci_x D)).
Definition cn_at_copy2 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 own : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(32, cn_F D); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [r1] own /\
  PresetHullBudget.hull_budget S (cn_hrest_cpy1 (ci_x D)).
Lemma cn_at_copy2_R_wle : forall D fxk ly S Hp W regs mem md k r1 own,
  cn_at_copy2 D fxk ly S Hp W regs mem md k r1 own = cn_at_copy2R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 own.
Proof. reflexivity. Qed.
(* CN_COPY3 (CA4 start): copy 2 done, slots 24 = r1 / 40 = r2 written (0x81ad8 / 0x81adc), r1 still in s5 *)
Definition cn_at_copy3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 own : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(24, r1); (32, cn_F D); (40, r2); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [r1; r2] own /\
  PresetHullBudget.hull_budget S (cn_hrest_cpy2 (ci_x D)).
Definition cn_at_copy3 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 own : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, r1); (23%bv, ci_data D)]) /\
  cn_slotsL D W mem [(24, r1); (32, cn_F D); (40, r2); (80, cn_F D)] /\
  cn_early D ly S Hp W mem [r1; r2] own /\
  PresetHullBudget.hull_budget S (cn_hrest_cpy2 (ci_x D)).
Lemma cn_at_copy3_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 own,
  cn_at_copy3 D fxk ly S Hp W regs mem md k r1 r2 own =
  cn_at_copy3R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 own.
Proof. reflexivity. Qed.

(* ---- THE CUTS ---- *)
(* CN_INIT (CA5, the third copy non-NULL): s3 = d3, s4 = size, s5 = d2, s6 = r3, s7 = data, s9 = d1; the structs not
   yet opened; the byte at g_own_ran_out is own0, and own0 = 0 says the first two copies are non-NULL (each NULL arm
   stores 1 there, 0x81acc / 0x81b14); own0 <> 0 says one was refused, which is dead at a consumer run (cn_cdead) *)
Definition cn_at_initR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, ci_data D); (25%bv, cn_d1 D)]) /\
  cn_slots D W mem r1 r2 /\
  cn_copy D ly S Hp W mem r1 /\ cn_copy D ly S Hp W mem r2 /\ cn_copy D ly S Hp W mem r3 /\ r3 <> 0 /\
  0 <= own0 < 256 /\ val_mem SEGS (rdW W mem) (VAL (A_OBJ 13)) 1 own0 /\ (own0 = 0 -> r1 <> 0 /\ r2 <> 0) /\
  (own0 <> 0 -> cn_cdead D) /\
  Hp = ci_Hp D /\
  prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own0 /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ablocks B (ci_ly D) (ci_S D)) /\
  room_live_cf S /\ cn_prog D (cn_cevs D r1 r2 r3) S /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Definition cn_at_init (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, ci_data D); (25%bv, cn_d1 D)]) /\
  cn_slots D W mem r1 r2 /\
  cn_copy D ly S Hp W mem r1 /\ cn_copy D ly S Hp W mem r2 /\ cn_copy D ly S Hp W mem r3 /\ r3 <> 0 /\
  0 <= own0 < 256 /\ val_mem SEGS (rdW W mem) (VAL (A_OBJ 13)) 1 own0 /\ (own0 = 0 -> r1 <> 0 /\ r2 <> 0) /\
  (own0 <> 0 -> cn_cdead D) /\
  Hp = ci_Hp D /\
  prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own0 /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ablocks B (ci_ly D) (ci_S D)) /\
  room_live_cf S /\ cn_prog D (cn_cevs D r1 r2 r3) S /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Lemma cn_at_init_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cn_at_init D fxk ly S Hp W regs mem md k r1 r2 r3 own0 =
  cn_at_initR (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof. reflexivity. Qed.
(* CN_INIT3 (CA5, the third copy NULL): as CN_INIT with r3 = 0; s3 = size + 16 (the request), s6 = 0, s10 = d3; the
   third copy was refused, so the refusal is dead at a consumer run (cn_cdead) *)
Definition cn_at_init3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, 0);
                                (23%bv, ci_data D); (25%bv, cn_d1 D); (26%bv, cn_d3 D)]) /\
  cn_slots D W mem r1 r2 /\
  cn_copy D ly S Hp W mem r1 /\ cn_copy D ly S Hp W mem r2 /\
  Hp = ci_Hp D /\
  (* the store of 1 to g_own_ran_out is CA5's first store (0x81c20), so here the ledger's own cell holds the byte of
     CA0-CA4, whatever it is *)
  (exists own, prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own) /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 0 ++ ablocks B (ci_ly D) (ci_S D)) /\
  room_live_cf S /\ cn_prog D (cn_cevs D r1 r2 0) S /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  cn_cdead D /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Definition cn_at_init3 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, 0);
                                (23%bv, ci_data D); (25%bv, cn_d1 D); (26%bv, cn_d3 D)]) /\
  cn_slots D W mem r1 r2 /\
  cn_copy D ly S Hp W mem r1 /\ cn_copy D ly S Hp W mem r2 /\
  Hp = ci_Hp D /\
  (* the store of 1 to g_own_ran_out is CA5's first store (0x81c20), so here the ledger's own cell holds the byte of
     CA0-CA4, whatever it is *)
  (exists own, prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own) /\
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 0 ++ ablocks B (ci_ly D) (ci_S D)) /\
  room_live_cf S /\ cn_prog D (cn_cevs D r1 r2 0) S /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX /\
  cn_cdead D /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Lemma cn_at_init3_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2,
  cn_at_init3 D fxk ly S Hp W regs mem md k r1 r2 = cn_at_init3R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2.
Proof. reflexivity. Qed.
(* the last-read flag and the copies: a byte (CnoA678's finding: the code tests the register); own0 = 0 says no copy
   is NULL; own0 <> 0 is still the byte in memory *)
Definition cn_flag0 (D : cn_in) (W : world SEGS) (mem : word -> option byte) (r1 r2 r3 own0 : Z) : Prop :=
  0 <= own0 < 256 /\
  (own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) /\
  (own0 <> 0 -> val_mem SEGS (rdW W mem) (VAL (A_OBJ 13)) 1 own0).
(* CN_READ1 (CA6, the return site of the third zeroing memset, before `li s7, -1`): the structs open and zero,
   s10 = own0, s3 = d3, s4 = size, s5 = d2, s6 = r3, s7 = data, s9 = d1; the granted copies' events made *)
Definition cn_at_read1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, ci_data D); (25%bv, cn_d1 D); (26%bv, own0)]) /\
  cn_slots D W mem r1 r2 /\ cn_flag0 D W mem r1 r2 r3 own0 /\ Hp = ci_Hp D /\ (own0 <> 0 -> cn_cdead D) /\
  cn_prog D (cn_cevs D r1 r2 r3) S /\
  cn_mid D ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) (ci_ran D) own0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Definition cn_at_read1 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, ci_data D); (25%bv, cn_d1 D); (26%bv, own0)]) /\
  cn_slots D W mem r1 r2 /\ cn_flag0 D W mem r1 r2 r3 own0 /\ Hp = ci_Hp D /\ (own0 <> 0 -> cn_cdead D) /\
  cn_prog D (cn_cevs D r1 r2 r3) S /\
  cn_mid D ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) (ci_ran D) own0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Lemma cn_at_read1_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cn_at_read1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 =
  cn_at_read1R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof. reflexivity. Qed.
(* CN_READ2 (CA7): reading 1 done (rc1 in s7, its struct st1, its grant o1, its free-order tie) when every copy is
   non-NULL (own0 = 0); after a NULL copy (own0 <> 0, A' reaches this cut too) reading 1 was skipped, no reading event
   was made, and the refusal is dead at a consumer run. g_ran_out is 1 exactly when reading 1 ran out; s10 = r1 *)
Definition cn_at_read2 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 own0 rc1 : Z) (st1 : cn_st) (o1 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 2 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, rc1); (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ cn_flag0 D W mem r1 r2 r3 own0 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran own0 1 r1 r2 r3 st1 None None /\
  (own0 = 0 -> cn_prog D (cn_cevs D r1 r2 r3 ++ cn_pe D o1) S /\ ran = cn_ranz D o1 None None /\
     cn_rd D o1 st1 /\ cn_res D ran rc1 st1 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1) /\
  (own0 <> 0 -> cn_prog D (cn_cevs D r1 r2 r3) S /\ st1 = None /\ cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hrest_rd1 (ci_x D)).
Definition cn_at_read2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 own0 rc1 : Z) (st1 : cn_st) (o1 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 2 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, rc1); (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ cn_flag0 D W mem r1 r2 r3 own0 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran own0 1 r1 r2 r3 st1 None None /\
  (own0 = 0 -> cn_prog D (cn_cevs D r1 r2 r3 ++ cn_pe D o1) S /\ ran = cn_ranz D o1 None None /\
     cn_rd D o1 st1 /\ cn_res D ran rc1 st1 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1) /\
  (own0 <> 0 -> cn_prog D (cn_cevs D r1 r2 r3) S /\ st1 = None /\ cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hrest_rd1 (ci_x D)).
Lemma cn_at_read2_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1,
  cn_at_read2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1 =
  cn_at_read2R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1.
Proof. reflexivity. Qed.
(* CN_READ3 (CA8): reached only with own0 = 0 (every copy non-NULL); reading 2 done or skipped (rc2 in s9; its grant
   o2, None when skipped) *)
Definition cn_at_read3 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cn_st) (o1 o2 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 4 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, rc1); (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) S /\ ran = cn_ranz D o1 o2 None /\
  cn_rds2 D o1 o2 st1 st2 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None /\
  cn_res D ran rc1 st1 /\ cn_res D ran rc2 st2 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd2 (ci_x D)).
Definition cn_at_read3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cn_st) (o1 o2 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 4 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3);
                                (23%bv, rc1); (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) S /\ ran = cn_ranz D o1 o2 None /\
  cn_rds2 D o1 o2 st1 st2 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None /\
  cn_res D ran rc1 st1 /\ cn_res D ran rc2 st2 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd2 (ci_x D)).
Lemma cn_at_read3_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_at_read3 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 =
  cn_at_read3R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof. reflexivity. Qed.
(* CN_CMP (CA9): all three readings done or skipped (rc3 in s4), s5 = 1; the grants o1 o2 o0 (None for a skipped
   reading) *)
Definition cn_at_cmp (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 rc3 : Z) (st1 st2 st3 : cn_st) (o1 o2 o0 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, rc3); (21%bv, 1); (22%bv, r3);
                                (23%bv, rc1); (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0 /\
  cn_rds3 D o1 o2 o0 st1 st2 st3 /\
  cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\ cn_fo D W mem Lam o0 (cn_d3 D) st3 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 /\
  cn_res D ran rc1 st1 /\ cn_res D ran rc2 st2 /\ cn_res D ran rc3 st3 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
Definition cn_at_cmpR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 rc3 : Z) (st1 st2 st3 : cn_st) (o1 o2 o0 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, rc3); (21%bv, 1); (22%bv, r3);
                                (23%bv, rc1); (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0 /\
  cn_rds3 D o1 o2 o0 st1 st2 st3 /\
  cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\ cn_fo D W mem Lam o0 (cn_d3 D) st3 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 /\
  cn_res D ran rc1 st1 /\ cn_res D ran rc2 st2 /\ cn_res D ran rc3 st3 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
Lemma cn_at_cmp_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1
  o2 o0,
  cn_at_cmp D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 =
  cn_at_cmpR (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Proof. reflexivity. Qed.
(* CN_FREE (CA10): s9 = d1, s3 = d3, s6 = r3, s10 = r1, s5 = r; slots 40 r2, 48 d2. THE r FACT over ownl, the
   g_own_ran_out byte the code last read, which the ledger's own cell ties to the current memory. When no copy was
   refused (ownl = 0, the only arm the text's position clause covers), the readings' grants, their structs, their
   free-order ties and the events made since entry; after a refused copy (ownl <> 0) the readings were skipped, so the
   structs are zero and the events made are the granted copies' (tpj_free_specX's class-24 bound at each pj_free call
   comes from that live set in this arm too), and the refusal is dead at a consumer run (cn_cdead) *)
Definition cn_at_freeR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 r ownl : Z) (st1 st2 st3 : cn_st) (o1 o2 o0 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(19%bv, cn_d3 D); (21%bv, r); (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran ownl 3 r1 r2 r3 st1 st2 st3 /\
  0 <= ownl < 256 /\ ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) /\
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0 /\
     cn_rds3 D o1 o2 o0 st1 st2 st3 /\
     cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\ cn_fo D W mem Lam o0 (cn_d3 D) st3) /\
  (ownl <> 0 -> cn_prog D (cn_cevs D r1 r2 r3) S /\ st1 = None /\ st2 = None /\ st3 = None /\ cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
Definition cn_at_free (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 r ownl : Z) (st1 st2 st3 : cn_st) (o1 o2 o0 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(19%bv, cn_d3 D); (21%bv, r); (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\
  cn_mid D ly S Hp W mem Lam peak cnt ran ownl 3 r1 r2 r3 st1 st2 st3 /\
  0 <= ownl < 256 /\ ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) /\
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0 /\
     cn_rds3 D o1 o2 o0 st1 st2 st3 /\
     cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\ cn_fo D W mem Lam o0 (cn_d3 D) st3) /\
  (ownl <> 0 -> cn_prog D (cn_cevs D r1 r2 r3) S /\ st1 = None /\ st2 = None /\ st3 = None /\ cn_cdead D) /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
Lemma cn_at_free_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cn_at_free D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 =
  cn_at_freeR (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Proof. reflexivity. Qed.

(* the three parse_noting call states (callee entry, ra = the return site), each the read cut's facts there: the
   reading is made only when the guard found g_ran_out = 0 and every copy non-NULL *)
Definition cn_at_pn1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 : Z) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET1); (10%bv, r1); (11%bv, cn_size D); (12%bv, cn_d1 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, -1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ Hp = ci_Hp D /\
  cn_prog D (cn_cevs D r1 r2 r3) S /\
  cn_mid D ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) 0 0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Definition cn_at_pn1 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 : Z) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 0 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET1); (10%bv, r1); (11%bv, cn_size D); (12%bv, cn_d1 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, -1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ Hp = ci_Hp D /\
  cn_prog D (cn_cevs D r1 r2 r3) S /\
  cn_mid D ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) 0 0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cn_hrest_copies (ci_x D)).
Lemma cn_at_pn1_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cn_at_pn1 D fxk ly S Hp W regs mem md k r1 r2 r3 = cn_at_pn1R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3.
Proof. reflexivity. Qed.
Definition cn_at_pn2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cn_st) (o1 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 2 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET2); (10%bv, r2); (11%bv, cn_size D); (12%bv, cn_d2 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, rc1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_pe D o1) S /\ cn_ro D o1 = false /\ cn_rd D o1 st1 /\
  cn_fo D W mem Lam o1 (cn_d1 D) st1 /\
  cn_mid D ly S Hp W mem Lam peak cnt 0 0 1 r1 r2 r3 st1 None None /\ cn_res D 0 rc1 st1 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd1 (ci_x D)).
Definition cn_at_pn2 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cn_st) (o1 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 2 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET2); (10%bv, r2); (11%bv, cn_size D); (12%bv, cn_d2 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D); (22%bv, r3); (23%bv, rc1);
                                (25%bv, cn_d1 D); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_pe D o1) S /\ cn_ro D o1 = false /\ cn_rd D o1 st1 /\
  cn_fo D W mem Lam o1 (cn_d1 D) st1 /\
  cn_mid D ly S Hp W mem Lam peak cnt 0 0 1 r1 r2 r3 st1 None None /\ cn_res D 0 rc1 st1 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd1 (ci_x D)).
Lemma cn_at_pn2_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cn_at_pn2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 =
  cn_at_pn2R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Proof. reflexivity. Qed.
Definition cn_at_pn3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cn_st) (o1 o2 : option nat) : Prop :=
  cn_baseR R D fxk ly S Hp W regs mem md k 4 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET3); (10%bv, r3); (11%bv, cn_size D); (12%bv, cn_d3 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, 1); (22%bv, r3); (23%bv, rc1);
                                (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) S /\ cn_ro D o1 = false /\ cn_ro D o2 = false /\
  cn_rd D o1 st1 /\ cn_rd D o2 st2 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\
  cn_mid D ly S Hp W mem Lam peak cnt 0 0 2 r1 r2 r3 st1 st2 None /\ cn_res D 0 rc1 st1 /\ cn_res D 0 rc2 st2 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd2 (ci_x D)).
Definition cn_at_pn3 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cn_st) (o1 o2 : option nat) : Prop :=
  cn_base D fxk ly S Hp W regs mem md k 4 /\
  cn_regsat regs (cn_core D ++ [cn_s8; (1%bv, cn_pc CN_RET3); (10%bv, r3); (11%bv, cn_size D); (12%bv, cn_d3 D);
                                (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, 1); (22%bv, r3); (23%bv, rc1);
                                (25%bv, rc2); (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs2 D o1 o2) S /\ cn_ro D o1 = false /\ cn_ro D o2 = false /\
  cn_rd D o1 st1 /\ cn_rd D o2 st2 /\ cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\
  cn_mid D ly S Hp W mem Lam peak cnt 0 0 2 r1 r2 r3 st1 st2 None /\ cn_res D 0 rc1 st1 /\ cn_res D 0 rc2 st2 /\
  PresetHullBudget.hull_budget S (cn_hrest_rd2 (ci_x D)).
Lemma cn_at_pn3_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_at_pn3 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 =
  cn_at_pn3R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof. reflexivity. Qed.

(* ---- THE EXITS (the brief's FORWARD form, the internal file lane-102.md :29-30): a segment lemma reads
     forall P, srr_inv_laws SEGS P -> .. -> cn_pre CTX0 D -> cn_at_X D fxk .. -> P mem ->
     SRr SEGS W (cn_cfg fxk (cn_pc OFF_X) regs mem md) (fun W' c' => cn_ex_Y D W' c' /\ P (ms_mem (cfg_ms c')))
   with cn_ex_Y the cut it reaches (a disjunction when it has several exits). The float state at an exit is
   existential (parse_noting's post is apost_base_xF); cn_base carries frm_zero / fregs_kept_x against the entry's.
   The segments compose by SRr_bind. ---- *)
(* the exits of CA0 / CA1 / CA2 / CA3 (CA4's are cn_ex_init / cn_ex_init3) *)
Definition cn_ex_poisonR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cn_cfg SEGS fxk (cn_pc CN_POISON) regs mem md /\ cn_at_poisonR R D fxk ly S Hp W regs mem md k.
Definition cn_ex_poison (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cn_cfg SEGS fxk (cn_pc CN_POISON) regs mem md /\ cn_at_poison D fxk ly S Hp W regs mem md k.
Lemma cn_ex_poison_R_wle : forall D,
  cn_ex_poison D = cn_ex_poisonR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_copy1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY1) regs mem md /\ cn_at_copy1R R D fxk ly S Hp W regs mem md k.
Definition cn_ex_copy1 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY1) regs mem md /\ cn_at_copy1 D fxk ly S Hp W regs mem md k.
Lemma cn_ex_copy1_R_wle : forall D,
  cn_ex_copy1 D = cn_ex_copy1R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_copy2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 own,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY2) regs mem md /\ cn_at_copy2R R D fxk ly S Hp W regs mem md k r1 own.
Definition cn_ex_copy2 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 own,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY2) regs mem md /\ cn_at_copy2 D fxk ly S Hp W regs mem md k r1 own.
Lemma cn_ex_copy2_R_wle : forall D,
  cn_ex_copy2 D = cn_ex_copy2R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_copy3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 own,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY3) regs mem md /\ cn_at_copy3R R D fxk ly S Hp W regs mem md k r1 r2 own.
Definition cn_ex_copy3 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 own,
  c = @cn_cfg SEGS fxk (cn_pc CN_COPY3) regs mem md /\ cn_at_copy3 D fxk ly S Hp W regs mem md k r1 r2 own.
Lemma cn_ex_copy3_R_wle : forall D,
  cn_ex_copy3 D = cn_ex_copy3R (@wle SEGS) D.
Proof. reflexivity. Qed.
(* the exits of the CA0-CA4 stretch (entry SIGMA AS_check_no_overread under cn_pre -> one of these two) *)
Definition cn_ex_initR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cn_cfg SEGS fxk (cn_pc CN_INIT) regs mem md /\ cn_at_initR R D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Definition cn_ex_init (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cn_cfg SEGS fxk (cn_pc CN_INIT) regs mem md /\ cn_at_init D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Lemma cn_ex_init_R_wle : forall D,
  cn_ex_init D = cn_ex_initR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_init3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2,
  c = @cn_cfg SEGS fxk (cn_pc CN_INIT3) regs mem md /\ cn_at_init3R R D fxk ly S Hp W regs mem md k r1 r2.
Definition cn_ex_init3 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2,
  c = @cn_cfg SEGS fxk (cn_pc CN_INIT3) regs mem md /\ cn_at_init3 D fxk ly S Hp W regs mem md k r1 r2.
Lemma cn_ex_init3_R_wle : forall D,
  cn_ex_init3 D = cn_ex_init3R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_read1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ1) regs mem md /\ cn_at_read1R R D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Definition cn_ex_read1 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ1) regs mem md /\ cn_at_read1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Lemma cn_ex_read1_R_wle : forall D,
  cn_ex_read1 D = cn_ex_read1R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_pn1R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\ cn_at_pn1R R D fxk ly S Hp W regs mem md k r1 r2 r3.
Definition cn_ex_pn1 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\ cn_at_pn1 D fxk ly S Hp W regs mem md k r1 r2 r3.
Lemma cn_ex_pn1_R_wle : forall D,
  cn_ex_pn1 D = cn_ex_pn1R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_read2 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ2) regs mem md /\
  cn_at_read2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1.
Definition cn_ex_read2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ2) regs mem md /\
  cn_at_read2R R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1.
Lemma cn_ex_read2_R_wle : forall D,
  cn_ex_read2 D = cn_ex_read2R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_pn2R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\
  cn_at_pn2R R D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Definition cn_ex_pn2 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\
  cn_at_pn2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Lemma cn_ex_pn2_R_wle : forall D,
  cn_ex_pn2 D = cn_ex_pn2R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_read3 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ3) regs mem md /\
  cn_at_read3 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Definition cn_ex_read3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cn_cfg SEGS fxk (cn_pc CN_READ3) regs mem md /\
  cn_at_read3R R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Lemma cn_ex_read3_R_wle : forall D,
  cn_ex_read3 D = cn_ex_read3R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_pn3R (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\
  cn_at_pn3R R D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Definition cn_ex_pn3 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cn_cfg SEGS fxk (SIGMA AS_parse_noting) regs mem md /\
  cn_at_pn3 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Lemma cn_ex_pn3_R_wle : forall D,
  cn_ex_pn3 D = cn_ex_pn3R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_cmp (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  c = @cn_cfg SEGS fxk (cn_pc CN_CMP) regs mem md /\
  cn_at_cmp D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Definition cn_ex_cmpR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  c = @cn_cfg SEGS fxk (cn_pc CN_CMP) regs mem md /\
  cn_at_cmpR R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Lemma cn_ex_cmp_R_wle : forall D,
  cn_ex_cmp D = cn_ex_cmpR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cn_ex_freeR (R : world SEGS -> world SEGS -> Prop)
  (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  c = @cn_cfg SEGS fxk (cn_pc CN_FREE) regs mem md /\
  cn_at_freeR R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Definition cn_ex_free (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  c = @cn_cfg SEGS fxk (cn_pc CN_FREE) regs mem md /\
  cn_at_free D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Lemma cn_ex_free_R_wle : forall D,
  cn_ex_free D = cn_ex_freeR (@wle SEGS) D.
Proof. reflexivity. Qed.


Lemma cn_at_poisonR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k,
  cn_at_poisonR R1 D fxk ly S Hp W regs mem md k -> cn_at_poisonR R2 D fxk ly S Hp W regs mem md k.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_copy1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k,
  cn_at_copy1R R1 D fxk ly S Hp W regs mem md k -> cn_at_copy1R R2 D fxk ly S Hp W regs mem md k.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_copy2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 own,
  cn_at_copy2R R1 D fxk ly S Hp W regs mem md k r1 own -> cn_at_copy2R R2 D fxk ly S Hp W regs mem md k r1 own.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 own (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_copy3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 own,
  cn_at_copy3R R1 D fxk ly S Hp W regs mem md k r1 r2 own -> cn_at_copy3R R2 D fxk ly S Hp W regs mem md k r1 r2 own.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 own (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_initR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cn_at_initR R1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  cn_at_initR R2 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_init3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2,
  cn_at_init3R R1 D fxk ly S Hp W regs mem md k r1 r2 -> cn_at_init3R R2 D fxk ly S Hp W regs mem md k r1 r2.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_read1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cn_at_read1R R1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  cn_at_read1R R2 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_read2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1,
  cn_at_read2R R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1 ->
  cn_at_read2R R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1
  (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_read3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_at_read3R R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  cn_at_read3R R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2
  (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_cmpR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  cn_at_cmpR R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 ->
  cn_at_cmpR R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0
  (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_freeR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cn_at_freeR R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 ->
  cn_at_freeR R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0
  (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_pn1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cn_at_pn1R R1 D fxk ly S Hp W regs mem md k r1 r2 r3 -> cn_at_pn1R R2 D fxk ly S Hp W regs mem md k r1 r2 r3.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_pn2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cn_at_pn2R R1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 ->
  cn_at_pn2R R2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_at_pn3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_at_pn3R R1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  cn_at_pn3R R2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2
  (HB & HR). split; [|exact HR].
apply (cn_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cn_ex_poisonR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_poisonR R1 D W c -> cn_ex_poisonR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k. split; [exact E|].
apply (cn_at_poisonR_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_copy1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_copy1R R1 D W c -> cn_ex_copy1R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k. split; [exact E|].
apply (cn_at_copy1R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_copy2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_copy2R R1 D W c -> cn_ex_copy2R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & own & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, own. split; [exact E|].
apply (cn_at_copy2R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_copy3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_copy3R R1 D W c -> cn_ex_copy3R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & own & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, own. split; [exact E|].
apply (cn_at_copy3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_initR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_initR R1 D W c -> cn_ex_initR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3, own0. split; [exact E|].
apply (cn_at_initR_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_init3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_init3R R1 D W c -> cn_ex_init3R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2. split; [exact E|].
apply (cn_at_init3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_read1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_read1R R1 D W c -> cn_ex_read1R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3, own0. split; [exact E|].
apply (cn_at_read1R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_pn1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_pn1R R1 D W c -> cn_ex_pn1R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3. split; [exact E|].
apply (cn_at_pn1R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_read2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_read2R R1 D W c -> cn_ex_read2R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & own0 & rc1 & st1 & o1 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, own0, rc1, st1, o1. split; [exact E|].
apply (cn_at_read2R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_pn2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_pn2R R1 D W c -> cn_ex_pn2R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & st1 & o1 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, rc1, st1, o1. split; [exact E|].
apply (cn_at_pn2R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_read3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_read3R R1 D W c -> cn_ex_read3R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & st1 & st2 & o1 &
   o2 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, rc1, rc2, st1, st2, o1,
  o2. split; [exact E|].
apply (cn_at_read3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_pn3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_pn3R R1 D W c -> cn_ex_pn3R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & rc2 & st1 & st2 & o1 & o2 & E &
   HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, rc1, rc2, st1, st2, o1, o2. split; [exact E|].
apply (cn_at_pn3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_cmpR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_cmpR R1 D W c -> cn_ex_cmpR R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & rc3 & st1 & st2 &
   st3 & o1 & o2 & o0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, rc1, rc2, rc3, st1, st2, st3, o1, o2,
  o0. split; [exact E|].
apply (cn_at_cmpR_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_ex_freeR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_freeR R1 D W c -> cn_ex_freeR R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & r & ownl & st1 & st2 & st3 &
   o1 & o2 & o0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, r, ownl, st1, st2, st3, o1, o2,
  o0. split; [exact E|].
apply (cn_at_freeR_mono R1 R2 H12). exact HA.
Qed.
Lemma cn_postR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_postR R1 D W c -> cn_postR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly' & S' & Hp' & regs' & mem' & md' & k & WS & E & Hz & Hfk & HP & HJ & Hr & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k, WS.
split; [exact E|]. split; [exact Hz|]. split; [exact Hfk|]. split; [exact HP|]. split; [|split; [exact Hr | exact HQ]].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.
Lemma cn_ex_retR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cn_ex_retR R1 D W c -> cn_ex_retR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly' & S' & Hp' & regs' & mem' & md' & k & WS & E & Hz & Hfk & HP & HJ & Hr & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k, WS.
split; [exact E|]. split; [exact Hz|]. split; [exact Hfk|]. split; [exact HP|]. split; [|split; [exact Hr | exact HQ]].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.

End cn.
