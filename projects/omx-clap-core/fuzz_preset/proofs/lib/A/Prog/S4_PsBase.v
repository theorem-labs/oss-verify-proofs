(* fuzz_preset lib/A, slice S4 (parse_string, 389 instructions): the walk's SHARED BASE.
   The goal is the kit's tparse_string_specX (lib/A/PRH_FnReader.v f1ae32e3b2cd, as the kit's cut 7cdbb61b5fa0 carries it),
   proved at the ONE program listing (lib/A/Listing_prog.v 7ed1529926bd + PAImg_prog.v 505a51ff7d08, the cut's)
   with the listing engine (lib/Reusable/YC80x.v, YC1fPx.v, YCbqGcall.v). FILE SET: the cut's tree (YCbqG blob
   219748197d6b, AR_laws_x with hl); the unit's set of record at 06:3xZ was engine files and YCbqG.v by path from
   a working branch 63997a07aa6 + the kit walkkit b7722372682 + listing 7c8ffeba5035. This slice's caller-window discharge kit
   (lib/A/Prog/PRW_CallerJ.v) and the S7b walk's PRW_StepKit.v.
   parse_string writes its caller's cursor word in->p ABOVE its entry sp, so the kit owner states it in the caller-window form
   fpostW (PRH_Base.v): the journal runs at (STK_parse_string + e) (sp + e), FP is [(q, q + 8)], and fpostW's
   extension clause ([sp, sp + e) outside FP unchanged) is carried across the walk by cj_kept (PRW_CallerJ.v) and
   closed by fpostW_x_of_kept.
   THE CUTS. One lemma per stretch between these program points, each stretch ending in the SAME final post
   (ps_post), so the stretches compose by `apply` with no continuation quantifier. Offsets are DERIVED (byte offsets
   inside the function; the entry is the listing's A_prog_slot AS_parse_string, never a typed address):
     PS_ENTRY  0     the entry
     PS_SCAN   132   the scan loop head            (the `srli a3, a0, 3` of the shadow check)
     PS_MALLOC 200   the fuzz_malloc call site     (a PCall slot)
     PS_DEC    328   the decode loop head
     PS_HEX    452   the four-hex-digit loop head
     PS_FREE   1280  the fuzz_free call site       (a PCall slot)
     PS_RET0   1284  the NULL return               (`li s2, 0`, the join of every refusing path)
     PS_RETOK  1352  the success tail              (the shadow check; the NUL store is at 1368)
   Every numeral here is a DERIVED byte offset inside parse_string or a LENGTH; none is an ADDRESS.
   MEASUREMENT SCOPE: every code fact cited here (cut offsets, register maps, the chain's discharge routes at the two
   callers) is A-MEASURED from the neutral listing of image A; image B is UNMEASURED by this lane (BParseString
   measures B, including B's parse_value prologue and pj_parse's call, before any B twin cites a route).
   The harness-block shadow law is no longer a stand-in: it is the journal's law field 14 alx_hshadow (YCbqG walks-new
   d15706bda36, adopted verbatim from the S7b walk's PRW_HShadow.v), so LAWS is taken at hl := cf_head.
   #102 MOVE (a Theorem Labs lane PsRebindA, 2026-10-29): image A (asan d83eb25d) -> A' (asan 1be0f53d, twin bff8519bbe3e). The
   lane files are relocated from the Qed donor walk-S4 preset-tree-at-2026-10-29T15-36-18Z.tsv (sha256 88f8a644e245; internal record) by alreloc c4338d099cfb8025 (3 comment numerals
   moved); the A' listing is PAImg_prog 505a51ff7d08 (parse_string's slot 6363, 0x8794c).
   AT THE KIT'S CUT (a Theorem Labs lane PsRebindA, 2026-10-30): a working branch 7cdbb61b5fa0 merged forward into the
   row's prep head preset-tree-at-2026-10-30T03-26-38Z.tsv (sha256 9eaa45cdfc48; internal record), every path but the lane files at the cut's blob (PRH_FnReader f1ae32e3b2cd,
   PRH_FnAlloc 4d8aeba047e5, PRH_Base ef7c8ca98529, the P'' set with AR_laws_x's 25 fields). The text
   tparse_string_specX is POST-IMPLICATION (PRH_Base.v's THE TWO FAMILIES): no position and no run premise at entry;
   the two live counts are entry premises over the ALL-GRANTED events prhPs_evs x [] (PresetRun.pkR, ps_cnts); each
   post arm states the live requests (ps_live) and the position transfer (ps_rpos) over the arm's OWN events
   prhPs_evs x okA, keyed on the instance's outcomes. So the walk carries no position: ps_alloc carries fuzz_malloc's
   own transfer (ps_rpos_mal), the bad escape composes it with fuzz_free's (ps_rpos_snoc). Batch-2 ledger form: binders
   most own (pi_most / pi_own). fpre's FRM0-ENTRY conjunct (frm_zero of the section's fx) is passed to the four
   callee fpre's (ps_frm0). THE CURSOR SET CW (PRH_Base.v :1461-1486): the text takes prh_cw_ok (the slot of the
   former prh_cur_ok) and `wild_room (as_universe B) CW 0 (st_depot S)` at entry, and its post is BUDGETED,
   fpostWbm .. (wbudget CW 0) ..: ps_post / ps_postP are YCbqGwild.fpostW_xb at that budget, and the one cut a wild
   trace can reach (the NULL return after the bad escape's fuzz_free) carries a budgeted journal (ps_carryw /
   ps_carryPw). THE TOP (S4_PsTop.ps_K0_of_counts) IS THE KIT TEXT itself: the change from the earlier statement
   DRAFT_tparse_string_specX (deleted) was NOT a conversion (the kit's refused arm adds the outcome-exclusion conjunct :624-629
   and counts ((cnt + 1) mod 2 ^ 64) :634-635); both are proved, the exclusion from fuzz_malloc's outcome clause
   (ps_excl_of_malloc), the mod from prh_alloc_post's refusal arm.
   THE HULL BUDGET (lib/Spec/PresetHullBudget.v): the text takes `hull_budget S (prhPs_evs x [])` at entry (ps_pre's
   eighth conjunct, after the two live counts) and states `hull_used S S' (prhPs_evs x [])` in its post. The walk pays
   fuzz_malloc's budget [HMal ..] from it (ps_hull_mal) and the bad escape's fuzz_free's [] from what the malloc's use
   leaves (ps_hull_free); the cut layer's transfer ps_rpos carries the use since the entry, read at the all-granted
   list (ps_hull_used_mal), and ps_QresK_of_res hands it to the post (ps_QK). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
(* the memnorm keep's runner side: the record srr_inv_laws is the engine's (YC80x.v, a Theorem Labs lane s1b 459129c18903),
   srr_inv_call / srr_inv_laws_imp / srr_inv_call_imp / srr_inv_laws_memnorm_k stay in YSRrMemnorm.v (5ffa8525936b);
   neither loads LiaTwx2 *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
(* the engine (YC80x, YC1fPx, YCbqGcall) is imported by the stretch files, not here: the contract states no run *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoomPos PresetRun PresetReqAt
  PresetHullBudget.
(* the live-request leaves of the text's room premises and post (qualified only) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ.
(* the P'' room count and the budgeted posts (the batch text's post is at wbudget CW 0), qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the re-hiding move: SRrG / SRr' / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf, and the kept relation over a
   world relation R (YCbqGcallW.cj_keptR, qualified: the kept relation this file names is PRW_CallerJ's cj_kept, the
   same body) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YCbqGcallW.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section ps. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the non-primary room invariant room_live_cf (PRH_Base.v's class PrhRoomLive): THE KIT'S NAMED HYPOTHESIS (the cut's
   instance PRH_Base.prh_room_live_a8 over a Theorem Labs lane's YGcfRoomLive.v); the texts and this walk are generic in it *)
Context {RL : PrhRoomLive}.
(* the image instances of record, bound ONCE here and never left to inference elsewhere in the slice: the sink SK
   stays an explicit Variable (there is no ASan sink instance in lib/A, so an inferred one would be the plain
   build's YI5b.src0_sink_head). *)
#[local] Instance PS_PrhImg : PrhImg := prh_img_A.
#[local] Instance PS_PAListing : PAListing A_prog_listing := PL_prog_A.
#[local] Instance PS_PAImg : PAImg A_prog_listing := PI_prog_A.
(* the image of record: the whole-program listing and its PAImg / PAListing instances, and PRH_Img's generated
   per-function data (frames, return sites, call sites) for image A *)
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
(* THE IMAGE GUARD (CrcBp's cr_segs_B template, the lead's 19:2xZ wrong-image-name trap): the segments every statement
   of this walk is over are image A''s loaded segments, by FULL name (the closure also loads plain-image modules, whose
   lib/Img0.v has a short name rsegs too) *)
Lemma ps_segs_A : segs = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs /\
  segs = OSSVerify.omx_clap_core.fuzz_preset.images.Asan.M.loaded_segments.
Proof. split; reflexivity. Qed.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PST := (prh_pst ).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept SK segs B PST).
#[local] Notation LEDGER := (prh_ledger B).

(* the journal's laws at the second instance's head length: field 14 alx_hshadow is the harness-block shadow law *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the program listing's library facts, over the PROGRAM instance (never a per-function listing: vacuous there) *)
Hypothesis TL : @PALib _ A_prog_listing PS_PAImg B.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).

(* ---- the callees' kit texts (lib/A/PRH_FnAlloc.v, PRH_FnReader.v), Section hypotheses until the layer composes ---- *)
Hypothesis HMALLOC : tfuzz_malloc_specX B ARx SK.
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
Hypothesis HHEX4 : thex4_specX B ARx SK.
Hypothesis HPUTU : tput_utf8_specX B ARx SK.

(* the harness-block shadow law, read off LAWS (field 14): the user bytes of a HARNESS block (head hidden, base in
   Hp) keep their shadow. ARx_shadow_law excludes every such block; this is the only way past a call. *)
Definition HSHADOW : ARx_hshadow_law segs B ARx cf_head := alx_hshadow segs B ARx LAWS.

(* ---- the walk's cut points: DERIVED byte offsets inside parse_string ---- *)
Definition PS_SLOT : nat := A_prog_slot AS_parse_string.
Definition PS_ENTRY : Z := 0.
Definition PS_SCAN : Z := 132.
Definition PS_MALLOC : Z := 200.
Definition PS_DEC : Z := 328.
Definition PS_HEX : Z := 452.
Definition PS_FREE : Z := 1280.
Definition PS_RET0 : Z := 1284.
Definition PS_RETOK : Z := 1352.
(* the listing offset of parse_string's entry: slot index x 4 (A_prog_slot of PAImg_prog.v) *)
Definition PS_OFF : Z := 4 * Z.of_nat PS_SLOT.
Lemma PS_entry_sigma : SIGMA AS_parse_string = BASE + PS_OFF.
Proof. vm_compute. reflexivity. Qed.
(* LENGTH: parse_string's own frame, the N of its `addi sp, sp, -N` (PRH_Img.v pi_frame F_parse_string) *)
Definition PS_FRAME : Z := pi_frame F_parse_string.

(* ---- THE ENTRY DATA: one record, so every stretch names the same entry state ---- *)
Record ps_in : Type := mkPsIn {
  pi_ly : alayout; pi_S : astate; pi_Hp : list Z; pi_W : world segs;
  pi_regs : bvmap 5 word; pi_mem : word -> option byte; pi_md : Model; pi_ch : list (Z * Z * Z);
  pi_e : Z; pi_q : Z; pi_text : Z; pi_len : Z; pi_p : Z; pi_d : Z; pi_tb : list Z;
  pi_Lam : list (Z * Z); pi_peak : Z; pi_cnt : Z; pi_fail : Z; pi_ran : Z;
  (* the text's ledger binders (#102 Batch 2; the cut's PRH_FnReader.v f1ae32e3b2cd :518): g_most and
     g_own_ran_out, which parse_string keeps *)
  pi_most : Z; pi_own : Z
}.
(* the text after the opening quote: the model's argument everywhere *)
Definition ps_x (D : ps_in) : list Z := rest_atR (pi_tb D) (pi_text D) (pi_p D + 1).

(* THE POSITION, POST-IMPLICATION (preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record), PRH_Base.v's THE TWO FAMILIES): no position at entry; a later state S
   transfers ANY position of ANY model run whose next events are E, by EXACTLY length E (the forall clause of each arm
   of the text's post, at the arm's own E). ps_rposK is that clause verbatim; the text's arms (ps_QresK) state it at
   prhPs_evs (ps_x D) okA. The names and bodies are the B' lane's (PstrBp's PS_Gen.v), so the two images read alike. *)
Definition ps_rposK (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
    PRH_Base.prh_run_at sm x os i E ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length E)%nat H0 hist' S.
(* THE CUT LAYER'S TRANSFER: the hull use since the entry, at most the ALL-GRANTED events prhPs_evs x [] (the text's
   hull_used conjunct; one list for every arm, since each arm's events are among them), and the position transfer by
   the arm's explicit event list E (E = [] where no allocator event happened, [HMal m] after a granted fuzz_malloc,
   [HMal m; HFr m] after it and the bad escape's fuzz_free, m = Q + 1 + cf_head); ps_QresK_of_res turns each list
   into the text's prhPs_evs (ps_x D) okA *)
Definition ps_rpos (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  PresetHullBudget.hull_used (pi_S D) S (prhPs_evs (ps_x D) []) /\ ps_rposK D E S.
(* THE LIVE REQUESTS after E (the text's Permutation clause, EXACT up to Permutation): each arm's own blocks facts give
   it, so the cut layer does not carry it (ps_QresK_of_res derives it) *)
Definition ps_live (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) E).
(* THE LIVE COUNTS (the text's two room premises, THE LIVE COUNTS AT THE INNER CALLS; they replace a Theorem Labs lane's
   counts_of_room_pos_rl): the secondary and the class-24 counts are bounded at EVERY state along the ALL-GRANTED
   events prhPs_evs x [] from the entry's live requests (PresetRun.pkR, the peak along the list) *)
Definition ps_cnts (D : ps_in) : Prop :=
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))
    (prhPs_evs (ps_x D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))
    (prhPs_evs (ps_x D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* tparse_string_specX's premises (the kit's cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd :517-577), at one record, in the
   text's order. Two conjuncts carry several of the text's premises: the fifth is prh_cw_ok (the cursor set CW, the
   slot prh_cur_ok vacated), and the eighth is the wild room `wild_room (as_universe B) CW 0 (st_depot S)` (:550)
   followed by the two live counts (ps_cnts) and the hull budget over the same all-granted events; the last is the
   request bound with prh_live_evs (:574-576) *)
Definition ps_pre (CTX : list (list Z)) (CW : list (list Z)) (D : ps_in) : Prop :=
  fpre B ARx STK_parse_string (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) /\
  prh_univ_closure B CTX /\
  (exists ch, achain (pi_ly D) (aview segs (w_H (pi_W D)) (pi_mem D)) (spZ (pi_regs D) - pi_frame F_parse_string)
     (prh_s0 F_parse_string (pi_q D)) ch) /\
  prh_cur_low (pi_W D) (pi_mem D) F_parse_string (pi_q D) /\ prh_cw_ok B CW (pi_W D) (pi_mem D) F_parse_string (pi_q D) /\
  spZ (pi_regs D) + 16 <= pi_q D /\
  room_live_cf (pi_S D) /\
  (YCbqGwild.wild_room (as_universe B) CW 0 (st_depot (pi_S D)) /\ ps_cnts D /\
   PresetHullBudget.hull_budget (pi_S D) (prhPs_evs (ps_x D) [])) /\
  getr (pi_regs D) 10 = w64 (pi_q D) /\
  pj_in_okR segs (rdW (pi_W D) (pi_mem D)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  pi_p D < pi_text D + pi_len D /\
  nth_error (pi_tb D) (Z.to_nat (pi_p D - pi_text D)) = Some 34 /\
  fwin (pi_ly D) (pi_W D) (pi_regs D) (pi_mem D) (pi_e D) /\
  spZ (pi_regs D) <= pi_q D /\ pi_q D + 24 <= spZ (pi_regs D) + pi_e D /\
  range_addressable (aview segs (w_H (pi_W D)) (pi_mem D)) SHADOW_OFF (pi_q D) 24 /\
  src_rd (pi_W D) (pi_mem D) (pi_text D) (pi_tb D) /\
  prhReader_home B (pi_ly D) (pi_S D) (pi_Hp D) (pi_Lam D) (pi_text D) (pi_len D) /\
  LEDGER (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  pi_cnt D + 1 < 2 ^ 64 - 1 /\
  (* the cut's last premise (PRH_FnReader f1ae32e3b2cd :575-576): the request bound, and the live room at EACH event of
     the all-granted run (prh_live_evs), which REPLACES the entry sum `blocks_bytes S + LIVE_parse_string Q <= LIVE_MAX` *)
  ((forall Q, PjGrammar.scan (ps_x D) = Some Q -> LIVE_parse_string Q < cf_malloc_max) /\
   prh_live_evs (pi_S D) (prhPs_evs (ps_x D) [])).
(* FRM0-ENTRY (fpre's last conjunct): the rounding mode of the section's fx is 0; every callee fpre the walk builds
   takes it from here *)
Lemma ps_frm0 : forall CTX CW D, ps_pre CTX CW D -> frm_zero (@YK11.fp_csr fx).
Proof. intros CTX CW D ((_ & _ & _ & _ & H) & _). exact H. Qed.
Lemma ps_cnts_of_pre : forall CTX CW D, ps_pre CTX CW D -> ps_cnts D.
Proof. intros CTX CW D (_ & _ & _ & _ & _ & _ & _ & (_ & H & _) & _). exact H. Qed.
Lemma ps_wild_of_pre : forall CTX CW D, ps_pre CTX CW D ->
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot (pi_S D)).
Proof. intros CTX CW D (_ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma ps_hull_of_pre : forall CTX CW D, ps_pre CTX CW D ->
  PresetHullBudget.hull_budget (pi_S D) (prhPs_evs (ps_x D) []).
Proof. intros CTX CW D (_ & _ & _ & _ & _ & _ & _ & (_ & _ & H) & _). exact H. Qed.

(* the post body of the CUT LAYER: the text's arms, each with its OWN explicit event list for the position and no
   live-request conjunct (ps_QresK_of_res derives it from the arm's blocks facts) *)
Definition ps_Qres (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  match PjGrammar.scan (ps_x D) with
  | None =>
      res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
      LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
      pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
      ps_rpos D [] S'
  | Some Q =>
      (pi_cnt D = pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D + 1) SIZE_MAXZ (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [] S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       (exists regsc memc mdc Wc cc,
          YG0dcf.malloc_cf_null_post segs B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc
            (Z.of_nat Q + 1 + cf_head) (PNull, S') Wc cc) /\
       rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
       (* THE OUTCOME (PRH_FnReader f1ae32e3b2cd :624-629): no model run whose next events are the all-granted ones
          meets this refused arm at a consumer position *)
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs (ps_x D) []) ->
          PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (ps_x D) [])) -> False) /\
       (* the ledger: fuzz_malloc's refusal arm verbatim (:634-635) *)
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Z.min SIZE_MAXZ (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))) ((pi_cnt D + 1) mod 2 ^ 64)
         (pi_fail D) (if Z.of_nat Q + 1 <=? pi_most D then 1 else pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [] S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ PjGrammar.decode (ps_x D) = None /\
       Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] S')
      \/
      (pi_cnt D <> pi_fail D /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode (ps_x D) = Some (s, r) /\
       Hp' = (res - cf_head) :: pi_Hp D /\
       ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       prhReader_vis W' mem' res (Z.of_nat Q + 1) /\
       pj_cbytesR segs (rdW W' mem') res s /\
       LEDGER ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D) /\
       ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] S')
  end.
(* THE TEXT'S ARMS (the kit's cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd :582-680), VERBATIM at one record: every arm
   states the live requests and the position after its own events prhPs_evs x okA, with okA the instance's outcomes on
   that arm ([] when no allocator call, [false] for a NULL, [true] for a block); ps_live / ps_rposK unfold to the text's
   Permutation and forall clauses *)
Definition ps_QresK (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  match PjGrammar.scan (ps_x D) with
  | None =>
      res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
      LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
      pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
      ps_live D (prhPs_evs (ps_x D) []) S' /\ ps_rposK D (prhPs_evs (ps_x D) []) S'
  | Some Q =>
      (pi_cnt D = pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D + 1) SIZE_MAXZ (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [false]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [false]) S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       (exists regsc memc mdc Wc cc,
          YG0dcf.malloc_cf_null_post segs B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc
            (Z.of_nat Q + 1 + cf_head) (PNull, S') Wc cc) /\
       rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs (ps_x D) []) ->
          PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (ps_x D) [])) -> False) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Z.min SIZE_MAXZ (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))) ((pi_cnt D + 1) mod 2 ^ 64)
         (pi_fail D) (if Z.of_nat Q + 1 <=? pi_most D then 1 else pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [false]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [false]) S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ PjGrammar.decode (ps_x D) = None /\
       Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [true]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [true]) S')
      \/
      (pi_cnt D <> pi_fail D /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode (ps_x D) = Some (s, r) /\
       Hp' = (res - cf_head) :: pi_Hp D /\
       ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       prhReader_vis W' mem' res (Z.of_nat Q + 1) /\
       pj_cbytesR segs (rdW W' mem') res s /\
       LEDGER ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [true]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [true]) S')
  end.
(* the text's hull use (its third post conjunct) with the text's arms: the last conjunct of ps_Q, so a stretch that
   closes the post builds it with ps_QresK_of_res alone *)
Definition ps_QK (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  PresetHullBudget.hull_used (pi_S D) S' (prhPs_evs (ps_x D) []) /\ ps_QresK D res ly' S' Hp' W' mem' md'.
(* the text's post, the hull use in the last conjunct (ps_QT below is the text's order) *)
Definition ps_Q (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
  blocks_bytes S' <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_QK D res ly' S' Hp' W' mem' md'.
(* the text's post in the text's conjunct order (PRH_FnReader.v tparse_string_specX: the hull use third) *)
Definition ps_QT (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
  PresetHullBudget.hull_used (pi_S D) S' (prhPs_evs (ps_x D) []) /\
  blocks_bytes S' <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_QresK D res ly' S' Hp' W' mem' md'.
Lemma ps_QT_of_Q : forall D ly' S' Hp' W' regs' mem' md',
  ps_Q D ly' S' Hp' W' regs' mem' md' -> ps_QT D ly' S' Hp' W' regs' mem' md'.
Proof.
intros D ly' S' Hp' W' regs' mem' md' (res & H1 & H2 & H3 & H4 & H5).
(* ps_QT is the text's post (tparse_string_specX's, in its conjunct order): BUILT BY NAME through the kit's projection
   layer (PRH_FnReader.v tpstP_Q_of_R from the record tpstP_R, field by field); md' is the one argument of the post
   that its body does not mention, so it is given *)
refine (tpstP_Q_of_R md' (res := res) _).
exact {| tpstP_ret := H1; tpstP_room := H2; tpstP_hull := H4; tpstP_bytes_le := H3; tpstP_arm := H5 |}.
Qed.

(* ---- the events, the live requests and the positions of each arm, from its own facts ---- *)
(* the live requests are the block sizes of ablocks (YGcfRoom.room_of_cf, YG0d.v ablocks) *)
Lemma ps_live_ab : forall ly S, PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (ablocks B ly S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.
Lemma ps_live_keep : forall D ly' S', ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) -> ps_live D [] S'.
Proof.
intros D ly' S' Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
unfold PresetReqAt.hlive_from. cbn [fold_left]. apply Permutation_refl.
Qed.
Lemma ps_live_bad : forall D ly' S' m, ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ->
  ps_live D [PresetReqAt.HMal m; PresetReqAt.HFr m] S'.
Proof.
intros D ly' S' m Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep PresetReqAt.rm1]. rewrite Z.eqb_refl.
apply Permutation_refl.
Qed.
Lemma ps_live_app : forall D ly' S' a m,
  ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(a, m)] -> ps_live D [PresetReqAt.HMal m] S'.
Proof.
intros D ly' S' a m Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep]. rewrite map_app. cbn [map snd].
apply Permutation_sym, Permutation_cons_append.
Qed.
(* a count over the live requests does not see their order (the cut layer's Permutation facts) *)
Lemma ps_cnt_perm : forall f l l', Permutation l l' -> PresetReqAt.cnt f l = PresetReqAt.cnt f l'.
Proof.
intros f l l' H. unfold PresetReqAt.cnt.
induction H as [| a u v _ IH | a b u | u v w _ IH1 _ IH2]; cbn [List.filter].
- reflexivity.
- destruct (f a); cbn [length]; lia.
- destruct (f a), (f b); cbn [length]; reflexivity.
- lia.
Qed.
(* the text's event lists on each arm (PRH_FnReader.v prhPs_evs) *)
Lemma ps_evs_none : forall x ok, PjGrammar.scan x = None -> prhPs_evs x ok = [].
Proof. intros x ok H. unfold prhPs_evs. rewrite H. reflexivity. Qed.
Lemma ps_evs_false : forall x Q, PjGrammar.scan x = Some Q -> prhPs_evs x [false] = [].
Proof. intros x Q H. unfold prhPs_evs. rewrite H. reflexivity. Qed.
Lemma ps_evs_bad : forall x Q, PjGrammar.scan x = Some Q -> PjGrammar.decode x = None ->
  prhPs_evs x [true] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)].
Proof. intros x Q H Hd. unfold prhPs_evs. rewrite H, Hd. reflexivity. Qed.
Lemma ps_evs_ok : forall x Q sr, PjGrammar.scan x = Some Q -> PjGrammar.decode x = Some sr ->
  prhPs_evs x [true] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)].
Proof. intros x Q sr H Hd. unfold prhPs_evs. rewrite H, Hd. reflexivity. Qed.
(* the position before any event, and no hull use *)
Lemma ps_rpos_nil : forall D, ps_rpos D [] (pi_S D).
Proof.
intros D. split; [apply PresetHullBudget.hull_used_refl|].
intros sm x os i H0 hist Hp _. exists hist. cbn [length]. rewrite Nat.add_0_r. exact Hp.
Qed.
(* one more event: a callee's post implication at its own one-event list [e] extends the transfer (the run premise
   splits by PRH_Base.prh_run_at_app_iff; the advances add up), and a callee that uses no hull (fuzz_free's post
   hull_used S1 S2 []) keeps the use *)
Lemma ps_rpos_snoc : forall D E e S1 S2, ps_rpos D E S1 -> PresetHullBudget.hull_used S1 S2 [] ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S1 -> PRH_Base.prh_run_at sm x os i [e] ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [e])%nat H0 hist' S2) ->
  ps_rpos D (E ++ [e]) S2.
Proof.
intros D E e S1 S2 [HU1 H1] HU2 H2. split.
{ pose proof (PresetHullBudget.hull_used_app (pi_S D) S1 S2 _ [] HU1 HU2) as HU. rewrite app_nil_r in HU. exact HU. }
intros sm x os i H0 hist Hp Hr.
apply (proj1 (prh_run_at_app_iff sm x os i E [e])) in Hr. destruct Hr as [Hr1 Hr2].
destruct (H1 sm x os i H0 hist Hp Hr1) as (hist1 & Hp1).
destruct (H2 sm x os (i + length E)%nat H0 hist1 Hp1 Hr2) as (hist2 & Hp2).
exists hist2. rewrite length_app, Nat.add_assoc. exact Hp2.
Qed.
(* THE REFUSED ARM'S OUTCOME CLAUSE from fuzz_malloc's own (PRH_FnAlloc 4d8aeba047e5 :302-312): the malloc's clause is
   stated over the one-event list [HMal m]; the text's over the all-granted list prhPs_evs x [], which starts with that
   event (a closed quote), so the run premise splits by prh_run_at_app_iff and the consumer premise restricts to its
   first event *)
Lemma ps_cons_from_le : forall sm x os i k k', (k' <= k)%nat ->
  PRH_Base.prh_cons_from sm x os i k -> PRH_Base.prh_cons_from sm x os i k'.
Proof. intros sm x os i k k' Hle H j e Hj He. exact (H j e ltac:(lia) He). Qed.
Lemma ps_evs_all_head : forall x Q, PjGrammar.scan x = Some Q ->
  exists rest, prhPs_evs x [] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ++ rest.
Proof.
intros x Q H. unfold prhPs_evs. rewrite H. cbn [nth].
exists (match PjGrammar.decode x with None => [PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] | Some _ => [] end).
reflexivity.
Qed.
(* THE HULL AT THE fuzz_malloc CALL: the text's budget over the all-granted events, at their first event (a closed
   quote: prhPs_evs x [] starts with the malloc's HMal, ps_evs_all_head) *)
Lemma ps_hull_mal : forall CTX CW D Q, ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  PresetHullBudget.hull_budget (pi_S D) [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)].
Proof.
intros CTX CW D Q HPRE HS. pose proof (ps_hull_of_pre CTX CW D HPRE) as HB.
destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest in HB.
exact (PresetHullBudget.hull_budget_infix (pi_S D) (pi_S D) [] [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] rest HB
  (PresetHullBudget.hull_used_refl (pi_S D) [])).
Qed.
(* fuzz_malloc's use (its post's hull_used at [HMal ..]) is a use at the all-granted list, which starts with it *)
Lemma ps_hull_used_mal : forall D Q S1, PjGrammar.scan (ps_x D) = Some Q ->
  PresetHullBudget.hull_used (pi_S D) S1 [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
  PresetHullBudget.hull_used (pi_S D) S1 (prhPs_evs (ps_x D) []).
Proof.
intros D Q S1 HS HU. destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest.
exact (PresetHullBudget.hull_used_infix (pi_S D) S1 [] [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] rest HU).
Qed.
(* THE ROOM AT THE MALLOC, from the cut's per-event premise at its first event (j = 0: the live bytes are the entry's,
   prh_live_at at 0 is blocks_bytes; PRH_Base.v's note on prh_live_evs) - the leaf's guarded `blocks_bytes S + (n +
   cf_head) <= LIVE_MAX` (PRH_FnAlloc 4d8aeba047e5 :283) *)
Lemma ps_live_at0 : forall (ly : alayout) S E, prh_live_at S E 0 = blocks_bytes S.
Proof.
intros ly S E. unfold prh_live_at. cbn [firstn]. rewrite PresetReqAt.hlive_from_nil.
rewrite (ps_live_ab ly S), (blocks_bytes_bsum B ly S). unfold bsum.
induction (ablocks B ly S) as [|b t IH]; cbn [map fold_right]; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma ps_live_bb : forall D Q, PjGrammar.scan (ps_x D) = Some Q -> prh_live_evs (pi_S D) (prhPs_evs (ps_x D) []) ->
  blocks_bytes (pi_S D) + (Z.of_nat Q + 1 + cf_head) <= LIVE_MAX.
Proof.
intros D Q HS HL. destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest).
pose proof (HL 0%nat (PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head))) as H0. rewrite Erest in H0.
specialize (H0 eq_refl). rewrite (ps_live_at0 (pi_ly D)) in H0. cbn [prh_ev_req] in H0. lia.
Qed.
Lemma ps_excl_of_malloc : forall D Q S1 res, PjGrammar.scan (ps_x D) = Some Q -> pi_cnt D <> pi_fail D -> res = 0 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
     PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
     PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)]) ->
     pi_cnt D <> pi_fail D ->
     res <> 0 /\
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)])%nat
       H0 hist' S1) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
    PRH_Base.prh_run_at sm x os i (prhPs_evs (ps_x D) []) ->
    PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (ps_x D) [])) -> False.
Proof.
intros D Q S1 res HS Hcf Hr HOUT sm x os i H0 hist Hp Hrun Hcons.
destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest in Hrun, Hcons.
apply (proj1 (prh_run_at_app_iff sm x os i _ rest)) in Hrun. destruct Hrun as [Hrun _].
apply (ps_cons_from_le sm x os i _ 1) in Hcons; [|rewrite length_app; cbn [length]; lia].
destruct (HOUT sm x os i H0 hist Hp Hrun Hcons Hcf) as [Hnz _]. exact (Hnz Hr).
Qed.
(* the cut layer's arms give the text's: the live requests from the blocks facts, the event lists by computation, and
   the hull use is every arm's ps_rpos's *)
Lemma ps_QresK_of_res : forall D res ly' S' Hp' W' mem' md',
  ps_Qres D res ly' S' Hp' W' mem' md' -> ps_QK D res ly' S' Hp' W' mem' md'.
Proof.
intros D res ly' S' Hp' W' mem' md' HQ. unfold ps_Qres in HQ. unfold ps_QK, ps_QresK.
(* each arm of the text's post is BUILT BY NAME through the kit's arm records (PRH_FnReader.v tpstP_RNone, tpstP_RSome1 ..
   tpstP_RSome4 and tpstP_ANone_of_R / tpstP_ASome1_of_R .. tpstP_ASome4_of_R); the live requests and the position
   at the arm's own events prhPs_evs (ps_x D) okA come from the arm's blocks facts and its explicit event list *)
destruct (PjGrammar.scan (ps_x D)) as [Q|] eqn:Hs.
2:{ destruct HQ as (H1 & H2 & H3 & H4 & H5 & HH & H6). split; [exact HH|].
    refine (tpstP_ANone_of_R _).
    assert (HL : ps_live D (prhPs_evs (ps_x D) []) S')
      by (rewrite (ps_evs_none (ps_x D) [] Hs); exact (ps_live_keep D ly' S' H3)).
    assert (HP : ps_rposK D (prhPs_evs (ps_x D) []) S') by (rewrite (ps_evs_none (ps_x D) [] Hs); exact H6).
    exact {| tpstPn_res0 := H1; tpstPn_hp := H2; tpstPn_ablocks := H3; tpstPn_ledger := H4; tpstPn_in_ok := H5;
             tpstPn_live := HL; tpstPn_pos := HP |}. }
destruct HQ as [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & HH & H8) |
  [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & HX & H8 & H9 & HH & H10) |
  [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & HH & H8) | (H1 & H2 & H3 & s & r & H4 & H5 & H6 & H7 & H8 & H9 & H10 & HH & H11)]]];
  (split; [exact HH|]).
- left. refine (tpstP_ASome1_of_R _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [false]) S')
    by (rewrite (ps_evs_false (ps_x D) Q Hs); exact (ps_live_keep D ly' S' H4)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [false]) S') by (rewrite (ps_evs_false (ps_x D) Q Hs); exact H8).
  exact {| tpstPs1_chosen := H1; tpstPs1_res0 := H2; tpstPs1_hp := H3; tpstPs1_ablocks := H4; tpstPs1_bytes := H5;
           tpstPs1_ledger := H6; tpstPs1_in_ok := H7; tpstPs1_live := HL; tpstPs1_pos := HP |}.
- right; left. refine (tpstP_ASome2_of_R _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [false]) S')
    by (rewrite (ps_evs_false (ps_x D) Q Hs); exact (ps_live_keep D ly' S' H4)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [false]) S') by (rewrite (ps_evs_false (ps_x D) Q Hs); exact H10).
  exact {| tpstPs2_notchosen := H1; tpstPs2_res0 := H2; tpstPs2_hp := H3; tpstPs2_ablocks := H4; tpstPs2_bytes := H5;
           tpstPs2_evidence := H6; tpstPs2_errno := H7; tpstPs2_outcome := HX; tpstPs2_ledger := H8;
           tpstPs2_in_ok := H9; tpstPs2_live := HL; tpstPs2_pos := HP |}.
- right; right; left. refine (tpstP_ASome3_of_R _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [true]) S')
    by (rewrite (ps_evs_bad (ps_x D) Q Hs H3); exact (ps_live_bad D ly' S' _ H5)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [true]) S') by (rewrite (ps_evs_bad (ps_x D) Q Hs H3); exact H8).
  exact {| tpstPs3_notchosen := H1; tpstPs3_res0 := H2; tpstPs3_bad := H3; tpstPs3_hp := H4; tpstPs3_ablocks := H5;
           tpstPs3_ledger := H6; tpstPs3_in_ok := H7; tpstPs3_live := HL; tpstPs3_pos := HP |}.
- right; right; right. refine (tpstP_ASome4_of_R (s := s) (r := r) _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [true]) S')
    by (rewrite (ps_evs_ok (ps_x D) Q (s, r) Hs H4); exact (ps_live_app D ly' S' _ _ H6)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [true]) S') by (rewrite (ps_evs_ok (ps_x D) Q (s, r) Hs H4); exact H11).
  exact {| tpstPs4_notchosen := H1; tpstPs4_res_min := H2; tpstPs4_res_align := H3; tpstPs4_decode := H4;
           tpstPs4_hp := H5; tpstPs4_ablocks := H6; tpstPs4_vis := H7; tpstPs4_cbytes := H8; tpstPs4_ledger := H9;
           tpstPs4_in_ok := H10; tpstPs4_live := HL; tpstPs4_pos := HP |}.
Qed.

(* THE ONE GOAL every stretch ends in: the text's conclusion at the entry state, BUDGETED at the cursor set CW (the
   batch text's post is fpostWbm .. (YCbqGwild.wbudget CW 0) ..: the journal from the entry at a budget WS of which
   it states wbudget CW 0 WS; only the bad escape's fuzz_free can store a trace outside the fixed ones) *)
Definition ps_post (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  YCbqGwild.fpostW_xb (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_Q D).
(* the text is m-form (fpostWbm .. (fQmn mem Q)); the stable ps_post (no keep) does not give it. The P-form post at
   P := ps_mn D does, by conversion (ps_postm_is_K0 below). *)
(* ps_post over a world relation R (a copy of ps_post's body at YCbqGwild.fpostW_xbR; ps_post is its instance at wle,
   ps_post_R_wle). A run that crosses the bad escape's fuzz_free ends at YA0nH.wle' segs RZ_cf (the kit's primed
   tparse_string_specX: SRr' segs RZ_cf with fpostWbm at wle'), so the stretches that may reach it end in
   ps_postR (wle' segs RZ_cf) *)
Definition ps_postR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) :
  world segs -> config -> Prop :=
  YCbqGwild.fpostW_xbR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_Q D).
Lemma ps_post_R_wle : forall CW D, ps_post CW D = ps_postR (@wle segs) CW D.
Proof. reflexivity. Qed.

(* the widened window the stretches' journals run at, and the body's sp *)
Definition PS_WSTK (D : ps_in) : Z := STK_parse_string + pi_e D.
Definition PS_WSP (D : ps_in) : Z := spZ (pi_regs D) + pi_e D.
Definition PS_SP (D : ps_in) : Z := spZ (pi_regs D) - PS_FRAME.

(* ---- what every cut carries: the journal from the entry state, the kept relation from the entry state (its out
   cells are the one caller word [q, q + 8)), the saved registers in the frame, and the text still readable ---- *)
Definition ps_saved (D : ps_in) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp := PS_SP D in
  val_mem segs (rdW W mem) (sp + 136) 8%nat (raZ (pi_regs D)) /\
  val_mem segs (rdW W mem) (sp + 128) 8%nat (bv_unsigned (getr (pi_regs D) 8)) /\
  val_mem segs (rdW W mem) (sp + 120) 8%nat (bv_unsigned (getr (pi_regs D) 9)) /\
  val_mem segs (rdW W mem) (sp + 112) 8%nat (bv_unsigned (getr (pi_regs D) 18)) /\
  val_mem segs (rdW W mem) (sp + 104) 8%nat (bv_unsigned (getr (pi_regs D) 19)) /\
  val_mem segs (rdW W mem) (sp + 96) 8%nat (bv_unsigned (getr (pi_regs D) 20)) /\
  val_mem segs (rdW W mem) (sp + 88) 8%nat (bv_unsigned (getr (pi_regs D) 21)) /\
  val_mem segs (rdW W mem) (sp + 80) 8%nat (bv_unsigned (getr (pi_regs D) 22)) /\
  val_mem segs (rdW W mem) (sp + 72) 8%nat (bv_unsigned (getr (pi_regs D) 23)) /\
  val_mem segs (rdW W mem) (sp + 64) 8%nat (bv_unsigned (getr (pi_regs D) 24)) /\
  val_mem segs (rdW W mem) (sp + 56) 8%nat (bv_unsigned (getr (pi_regs D) 25)) /\
  val_mem segs (rdW W mem) (sp + 48) 8%nat (bv_unsigned (getr (pi_regs D) 26)) /\
  val_mem segs (rdW W mem) (sp + 40) 8%nat (bv_unsigned (getr (pi_regs D) 27)).

Definition ps_carry (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) : Prop :=
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
(* the same carry with the journal at a BUDGET WS (YCbqG.ajournal_xw): only the NULL return after the bad escape's
   fuzz_free needs it, the one wild site of parse_string; ps_carry is ps_carryw at WS = [] by conversion *)
Definition ps_carryw (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xw (SK := SK) segs B PST ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
(* ps_carryw over a world relation R (a copy of its body: the journal at R, ajournal_xwR, and the kept relation at R,
   YCbqGcallW.cj_keptR; ps_carryw is its instance at wle, ps_carryw_R_wle): the cut after the bad escape's fuzz_free
   carries it at wle' segs RZ_cf *)
Definition ps_carrywR (R : world segs -> world segs -> Prop) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B PST ARx R (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
Lemma ps_carryw_R_wle : forall D ly S Hp W mem md k FPs WS,
  ps_carryw D ly S Hp W mem md k FPs WS = ps_carrywR (@wle segs) D ly S Hp W mem md k FPs WS.
Proof. reflexivity. Qed.
(* a kept relation at R1 is one at every R2 that contains R1 (only its world conjunct reads R) *)
Lemma ps_keptR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2,
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R1 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R2 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R1 R2 H12 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (H1 & H2 & H3 & H4).
exact (conj H1 (conj H2 (conj (H12 W W2 H3) H4))).
Qed.
(* the empty budget is within the cursor set's *)
Lemma ps_wb_nil : forall CW, YCbqGwild.wbudget CW 0 [].
Proof. intros CW. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia. Qed.

(* ---- the three registers the prologue sets and the whole function keeps (MEASURED, offsets 56-104): s8 (x24) the
   shadow base, s7 (x23) the shadow CELL of q, s9 (x25) the shadow cell of q + 8 ---- *)
Definition ps_sh_regs (D : ps_in) (regs : bvmap 5 word) : Prop :=
  getr regs 24 = w64 SHADOW_OFF /\
  getr regs 23 = w64 (SHADOW_OFF + pi_q D / 8) /\
  getr regs 25 = w64 (SHADOW_OFF + (pi_q D + 8) / 8).

(* ---- gp and tp: never written by parse_string, so at every cut they are the entry's (aregs_preserved asks them;
   PsRet's 04:5xZ finding) ---- *)
Definition ps_gptp (D : ps_in) (regs : bvmap 5 word) : Prop :=
  getr regs 3 = getr (pi_regs D) 3 /\ getr regs 4 = getr (pi_regs D) 4.

(* ---- the scan loop head (PS_SCAN): a0 = x the cursor, a1 = text + len, a2 = 34, s4 = p + 1, s0 = q, s1 = q + 8;
   the scan from p + 1 and the scan from x agree up to the bytes already passed ---- *)
Definition ps_at_scan (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
  ps_carry D ly S Hp W mem md 0 [] /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  (* before the malloc the walk has written only its own frame: the allocator state, the world and the harness
     facts are the entry's, read at the current memory (PsScan's 05:0xZ finding) *)
  ly = pi_ly D /\ S = pi_S D /\ Hp = pi_Hp D /\ W = pi_W D /\
  LEDGER ly S Hp W mem (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 10 = w64 x /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 12 = w64 34 /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 20 = w64 (pi_p D + 1) /\
  pi_p D + 1 <= x < pi_text D + pi_len D /\
  (* the scan from p + 1 is the scan from x shifted by the bytes passed; an equation, not an iff, so that it also
     covers scan = None (PsScan's 05:2xZ finding: the iff held vacuously at a cursor whose rest has no quote) *)
  PjGrammar.scan (ps_x D) =
    option_map (fun Q => (Q + Z.to_nat (x - (pi_p D + 1)))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) x)).

(* ---- the decode loop head (PS_DEC): s4 = r the read cursor, s3 = w the write cursor in the new block out,
   s2 = out, a1 = text + len, s0 = q, s9 = q + 8, s8 = the shadow base, and the constant registers the block at
   0x87a30-0x87a8c set. `done` is what decode has already written: the bytes at out, w - out of them, and decoding
   the text from p + 1 is those bytes followed by decoding from r. ---- *)
Definition ps_dec_rel (D : ps_in) (W : world segs) (mem : word -> option byte) (out w r : Z) (Q : nat) : Prop :=
  exists done,
    bytes_at W mem out done /\ Z.of_nat (length done) = w - out /\
    (forall sx rx, PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = Some (sx, rx) ->
       PjGrammar.decode (ps_x D) = Some (done ++ sx, rx)) /\
    (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None -> PjGrammar.decode (ps_x D) = None) /\
    pi_p D + 1 <= r <= pi_p D + 1 + Z.of_nat Q /\ out <= w /\ w - out <= r - (pi_p D + 1) /\
    (* decode stays in step with scan: the closing quote is Q - (r - (p + 1)) bytes on (PsDec's 05:1xZ finding;
       without it a cursor inside an escape makes ps_seg_dec false) *)
    PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) = Some (Q - Z.to_nat (r - (pi_p D + 1)))%nat.
(* the position after the one fuzz_malloc that returned a block: fuzz_malloc's own post implication at E = [HMal (Q + 1
   + cf_head)] (tfuzz_malloc_specX's res <> 0 arm), carried from the call to the bad escape's fuzz_free (which extends
   it, ps_rpos_snoc) and to the success return (the arm's position, as it is); the walk writes no allocator state in
   between *)
Definition ps_rpos_mal (D : ps_in) (Q : nat) (S : astate) : Prop :=
  ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] S.
(* the allocator state after the one fuzz_malloc: the new block is live, the ledger has it, the room is spent *)
Definition ps_alloc (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (out : Z) (Q : nat) : Prop :=
  pi_cnt D <> pi_fail D /\ 4096 + cf_head <= out /\ out mod 16 = 0 /\
  Hp = (out - cf_head) :: pi_Hp D /\
  ablocks B ly S = ablocks B (pi_ly D) (pi_S D) ++ [(out - cf_head, Z.of_nat Q + 1 + cf_head)] /\
  LEDGER ly S Hp W mem ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  prhReader_vis W mem out (Z.of_nat Q + 1) /\
  (* the position transfer of the call that made the block *)
  room_live_cf S /\ ps_rpos_mal D Q S /\
  (* the bytes the one malloc added to the live blocks, its head included (the post's prh_held clause) *)
  blocks_bytes S <= blocks_bytes (pi_S D) + (Z.of_nat Q + 1 + cf_head).
(* THE HULL AT THE BAD ESCAPE'S fuzz_free: the text's budget less the malloc's use (ps_alloc's ps_rpos_mal) is the
   free's budget for no event *)
Lemma ps_hull_free : forall CTX CW D Q S1, ps_pre CTX CW D -> ps_rpos_mal D Q S1 -> PresetHullBudget.hull_budget S1 [].
Proof.
intros CTX CW D Q S1 HPRE (HU & _).
exact (PresetHullBudget.hull_budget_used (pi_S D) S1 _ (ps_hull_of_pre CTX CW D HPRE) HU).
Qed.
(* the constant registers and stack words the block at offsets 228-324 sets, which the decode loop reads and
   put_utf8 clobbers and the block at 1048-1096 reloads (MEASURED). The three stack words are the surrogate
   constants: sp + 24 = 55296 (0xD800), sp + 16 = 56320 (0xDC00), sp + 8 = -56613888, the additive constant of
   PjGrammar.pair_cp (65536 - 55296 * 1024 - 56320). All LENGTH / WORD, none an address. *)
Definition ps_dec_consts (D : ps_in) (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word) : Prop :=
  getr regs 26 = w64 34 /\ getr regs 14 = w64 32 /\ getr regs 16 = w64 92 /\ getr regs 15 = w64 101 /\
  getr regs 17 = w64 91 /\ getr regs 5 = w64 47 /\ getr regs 6 = w64 98 /\ getr regs 7 = w64 8 /\
  getr regs 28 = w64 113 /\ getr regs 29 = w64 102 /\ getr regs 30 = w64 12 /\ getr regs 31 = w64 110 /\
  getr regs 27 = w64 10 /\ getr regs 21 = w64 114 /\ getr regs 1 = w64 116 /\
  val_mem segs (rdW W mem) (PS_SP D + 24) 8%nat 55296 /\
  val_mem segs (rdW W mem) (PS_SP D + 16) 8%nat 56320 /\
  val_mem segs (rdW W mem) (PS_SP D + 8) 8%nat (-56613888).
Definition ps_at_dec (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  ps_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  ps_dec_rel D W mem out w r Q.

(* ---- the NULL return (PS_RET0): s2 = 0 is about to be moved to a0 and the frame restored. Its arm fact is the
   whole of ps_Q but for the return value, which the stretch itself supplies: the predicate takes it as a parameter,
   so one lemma serves the five refusing paths. ---- *)
Definition ps_at_ret0 (CW : list (list Z)) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryw D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
(* the NULL return's cut over a world relation R (its carry at R, ps_carrywR; ps_at_ret0 is its instance at wle,
   ps_at_ret0_R_wle): the five refusing paths reach it at wle, the bad escape after its fuzz_free at wle' segs RZ_cf *)
Definition ps_at_ret0R (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) (ly : alayout)
  (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carrywR R D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
Lemma ps_at_ret0_R_wle : forall CW D ly S Hp W regs mem md,
  ps_at_ret0 CW D ly S Hp W regs mem md = ps_at_ret0R (@wle segs) CW D ly S Hp W regs mem md.
Proof. reflexivity. Qed.
(* ---- the success tail (PS_RETOK): the NUL store, the cursor store and the frame restore ---- *)
Definition ps_at_retok (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  r = pi_p D + 1 + Z.of_nat Q /\
  (exists s, PjGrammar.decode (ps_x D) = Some (s, rest_atR (pi_tb D) (pi_text D) (r + 1)) /\
     bytes_at W mem out s /\ Z.of_nat (length s) = w - out) /\
  (* decode never writes more bytes than it consumed, so the NUL at w is inside the block of Q + 1 bytes
     (WalkS4, after PsRet's 02:0xZ finding: without this clause the store's shadow check cannot be discharged) *)
  out <= w /\ w - out <= Z.of_nat Q.

(* ---- THE CHAIN FROM q AT A CALL. parse_string's four calls (fuzz_malloc 200, hex4 988, put_utf8 1044, fuzz_free
   1280) all run with s0 = q, so each callee's afn_pre_x needs a frame chain from q at the call's sp (the entry sp less
   the frame) in the CALL view. The kit's text (since walkkit 4eb03b7b7e8) gives it at the ENTRY view from prh_s0
   F_parse_string q (= q: pi_s0cur F_parse_string = Some 0 on image A), together with the gap bound spZ regs + 16 <= q.
   The stretches consume ONLY ps_chain0_of_pre / ps_qgap_of_pre / ps_chain_call. ---- *)
Definition ps_chain0 (D : ps_in) : Prop :=
  exists ch, achain (pi_ly D) (aview segs (w_H (pi_W D)) (pi_mem D)) (spZ (pi_regs D) - pi_frame F_parse_string)
    (prh_s0 F_parse_string (pi_q D)) ch.
Lemma ps_chain0_of_pre : forall CTX CW D, ps_pre CTX CW D -> ps_chain0 D.
Proof. intros CTX CW D (_ & _ & HCH & _). exact HCH. Qed.
(* the gap bound (the kit's text since 4eb03b7b7e8; WalkS4's q = sp + 8 counterexample made it a premise) *)
Definition ps_qgap (D : ps_in) : Prop := spZ (pi_regs D) + 16 <= pi_q D.
Lemma ps_qgap_of_pre : forall CTX CW D, ps_pre CTX CW D -> ps_qgap D.
Proof. intros CTX CW D (_ & _ & _ & _ & _ & HGAP & _). exact HGAP. Qed.
(* parse_string's chain starts at q itself (DERIVED from PRH_Img.v's pi_s0cur, image A) *)
Lemma ps_s0_q : forall q, prh_s0 F_parse_string q = q.
Proof. intros q. unfold prh_s0. replace (pi_s0cur F_parse_string) with (Some 0) by (vm_compute; reflexivity). lia. Qed.
(* the cursor store `sd s4, 0(s0)`, parse_string's ONLY write at or above its entry sp (the caller's word in->p, FP):
   A 0x87eb4, DERIVED offset PS_RETOK + 32 inside parse_string, on the success tail after every call *)
Definition PS_CURSOR_STORE : Z := 1384.
(* THE TRANSFER (a theorem under its agreement premise, which every call site meets): parse_string writes nothing at
   or above sp before its last call - only its frame [sp - 144, sp), the hex4 slot sp - 108 inside it, and the new
   heap block; the cursor store at PS_CURSOR_STORE (A 0x87eb4) comes after the last call. With the gap bound every byte
   the chain from q reads is at or above q - 16 >= sp, so the chain of the entry view is the chain of the call view. *)
Lemma ps_chain_call : forall D (rd : reader),
  ps_chain0 D -> ps_qgap D -> ly_top (pi_ly D) <= 2 ^ 64 ->
  (* agreement only on [sp, ly_top): a view wraps modulo 2 ^ 64, so an unbounded premise would also speak of the
     frame bytes the prologue wrote (PsScan's 08:3xZ finding); the chain reads stay below ly_top <= 2 ^ 64 *)
  (forall a, spZ (pi_regs D) <= a < ly_top (pi_ly D) -> rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) ->
  exists ch, achain (pi_ly D) rd (spZ (pi_regs D) - pi_frame F_parse_string) (pi_q D) ch.
Proof.
intros D rd (ch & HA) Hgap Htop Hrd. rewrite ps_s0_q in HA.
destruct HA as [(Hv & Ech) | (H1 & H2 & H3 & H4 & H5)]; exists ch; [left; exact (conj Hv Ech)|].
right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
eapply fpchain_ext; [|lia|exact H4].
intros a Ha Hat. unfold ps_qgap in Hgap. apply rdword_ext. intros k Hk. apply Hrd. lia.
Qed.

(* ---- the statements of the stretches. Each ends in the text's post, so they compose by `apply`. A stretch whose run
   may reach the bad escape's fuzz_free (entry, scan, dec; S4_PsDecKit's free, u and the loop's back edge) concludes
   SRr' segs RZ_cf with ps_postR (wle' segs RZ_cf); retok ends at wle; ret0 is reached on both sides of the free, so it
   has its form over R beside (ps_seg_ret0R; ps_seg_ret0 is its instance at wle). ---- *)
Definition ps_pc (off : Z) : Z := BASE + PS_OFF + off.
Definition ps_seg_entry (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D, ps_pre CTX CW D ->
  SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (SIGMA AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_scan (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md x, ps_pre CTX CW D -> ps_at_scan D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_SCAN) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_dec (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> ps_at_dec D ly S Hp W regs mem md out w r Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_ret0 (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0 CW D ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (ps_pc PS_RET0) regs mem md) (ps_post CW D).
Definition ps_seg_ret0R (R : world segs -> world segs -> Prop) (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0R R CW D ly S Hp W regs mem md ->
  SRrG segs R W (cfg_at segs (ps_pc PS_RET0) regs mem md) (ps_postR R CW D).
Lemma ps_seg_ret0_R_wle : forall CTX CW, ps_seg_ret0 CTX CW = ps_seg_ret0R (@wle segs) CTX CW.
Proof. reflexivity. Qed.
Definition ps_seg_retok (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> ps_at_retok D ly S Hp W regs mem md out w r Q ->
  SRr segs W (cfg_at segs (ps_pc PS_RETOK) regs mem md) (ps_post CW D).

(* ---- THE HAND-OFF to a stretch that may cross the free. A stretch runs at wle (SRr, the engine's runners and call
   rules) and hands its last state to the next stretch's SRr' fact (ps_hand); ps_SRr'_of_SRr turns the whole into
   SRr' (YA0nH.SRr_SRr', then SRrG_bind at wle'). ---- *)
Lemma ps_SRr'_of_SRr : forall W c (Q : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' Q) -> SRr' segs YGcfRehidePost.RZ_cf W c Q.
Proof.
intros W c Q H. unfold SRr'.
eapply (SRrG_bind segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf));
  [exact (SRr_SRr' segs YGcfRehidePost.RZ_cf W c _ H)|].
intros W' c' _ HQ. exact HQ.
Qed.
Lemma ps_hand : forall W c (Q : world segs -> config -> Prop),
  SRr' segs YGcfRehidePost.RZ_cf W c Q -> SRr segs W c (fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' Q).
Proof. intros W c Q H. apply SRr_ret. exact H. Qed.

(* ---- THE LEDGER THROUGH NAMED HELPERS ONLY. The four projections cite the kit's Section ledger_proj (PRH_Base.v
   ef7c8ca98529); ps_glob_keep_mb, ps_glob_cnt and ps_led_mk have no kit counterpart and are the only positional sites.
   The kit's Batch 2 (Option E, in decff67d721f) added g_most's and g_own_ran_out's cells to prh_glob (prh_most / prh_own)
   and the binders most own to prh_ledger; this block absorbed that change, the stretches only pass most own on. ---- *)
Lemma ps_vmem_keep : forall (W W' : world segs) m m' a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs (w_H W') m' (a + i) = aview segs (w_H W) m (a + i)) ->
  val_mem segs (rdW W m) a n v -> val_mem segs (rdW W' m') a n v.
Proof.
  intros W W' m m' a n v HA H k Hk. rewrite (mbyte_of_aview segs (w_H W) (w_H W') m m'); [exact (H k Hk)|].
  apply HA. lia.
Qed.
(* the global cells kept: every byte of the program's statics PST read the same *)
Lemma ps_glob_keep_mb : forall (W W' : world segs) mem mem' live peak cnt fail ran most own,
  (forall a, Exists (in_zr a) PST -> mbyte segs (rdW W' mem') a = mbyte segs (rdW W mem) a) ->
  prh_glob W mem live peak cnt fail ran most own -> prh_glob W' mem' live peak cnt fail ran most own.
Proof.
  intros W W' mem mem' live peak cnt fail ran most own HS HG.
  assert (HV : forall a n v, In (a, Z.of_nat n) PST -> val_mem segs (rdW W mem) a n v -> val_mem segs (rdW W' mem') a n v).
  { intros a n v Hin H k Hk. rewrite HS; [exact (H k Hk)|].
    apply Exists_exists. exists (a, Z.of_nat n). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. }
  destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & Grest).
  split; [apply HV; [cbn; tauto | exact G1]|]. split; [apply HV; [cbn; tauto | exact G2]|].
  split; [apply HV; [cbn; tauto | exact G3]|]. split; [apply HV; [cbn; tauto | exact G4]|].
  split; [apply HV; [cbn; tauto | exact G5]|].
  split; [split; [apply HV; [cbn; tauto | exact G6] | exact G6b]|].
  split; [split; [apply HV; [cbn; tauto | exact G7] | exact G7b]|]. exact Grest.
Qed.
Lemma ps_glob_keep : forall (W : world segs) mem mem' live peak cnt fail ran most own,
  (forall a, Exists (in_zr a) PST -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  prh_glob W mem live peak cnt fail ran most own -> prh_glob W mem' live peak cnt fail ran most own.
Proof.
  intros W mem mem' live peak cnt fail ran most own HS. apply ps_glob_keep_mb. intros a Ha.
  apply (mbyte_of_aview segs (w_H W) (w_H W) mem mem'). exact (HS a Ha).
Qed.
Lemma ps_glob_cnt : forall (W : world segs) mem live peak cnt fail ran most own,
  prh_glob W mem live peak cnt fail ran most own -> 0 <= cnt < 2 ^ 64.
Proof. intros W mem live peak cnt fail ran most own (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ps_led_glob : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> prh_glob W mem (Ledger.lsum Lam) peak cnt fail ran most own.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H.
exact (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own H).
Qed.
Lemma ps_led_nodup : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H.
exact (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own H).
Qed.
Lemma ps_led_blocks : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H.
exact (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own H).
Qed.
Lemma ps_led_heads : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> Permutation Hp (map (fun ak => fst ak - cf_head) Lam).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H.
exact (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own H).
Qed.
Lemma ps_led_mk : forall ly S Hp (W : world segs) mem Lam peak cnt fail ran most own,
  prh_glob W mem (Ledger.lsum Lam) peak cnt fail ran most own -> NoDup (map fst Lam) ->
  Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam ->
  Permutation Hp (map (fun ak => fst ak - cf_head) Lam) -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own.
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own H1 H2 H3 H4. exact (conj H1 (conj H2 (conj H3 H4))). Qed.

(* ==== THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z). An SRr post is OPAQUE once Qed, so an end-state invariant must
   be in the segment's statement: every stretch is stated over an invariant P of the memory with srr_inv_laws segs P,
   carried at every cut (ps_carryP: ps_carry with `/\ P mem` last) and at the post (ps_postP: ps_Q /\ P mem'). The
   function's top instantiates P ONCE as ps_mn D (memnorm of the entry memory gives memnorm at every later memory; the
   memnorm keep of the kit's m-form post). Every definition above stays byte-identical; the stable statements are the
   P := (fun _ => True) corollaries (ps_seg_*_of_True below). A segment that crosses a kit CALL also takes
   srr_inv_call segs P (a Theorem Labs lane 12:22Z; YSRrMemnorm.v blob a1c1ece77b14, a working branch 161f89a71b4d). ==== *)

(* the instantiation at the top: memnorm of the entry memory gives memnorm at m *)
Definition ps_mn (D : ps_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs (pi_mem D) -> YAkMemnorm.memnorm segs m.
Lemma ps_mn_laws : forall D, srr_inv_laws segs (ps_mn D).
Proof. intros D. exact (YSRrMemnorm.srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) (pi_mem D) (srr_inv_laws_memnorm_k segs)). Qed.
Lemma ps_mn_call : forall D, srr_inv_call segs (ps_mn D).
Proof. intros D. exact (YSRrMemnorm.srr_inv_call_imp segs (pi_mem D)). Qed.
Lemma ps_mn_entry : forall D, ps_mn D (pi_mem D).
Proof. intros D H. exact H. Qed.
(* the instantiation of the stable statements *)
Lemma srr_inv_laws_True : srr_inv_laws segs (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma srr_inv_call_True : srr_inv_call segs (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.

Section gp.
Variable P : (word -> option byte) -> Prop.
Definition ps_carryP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) : Prop :=
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
Definition ps_carryPw (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xw (SK := SK) segs B PST ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
(* ps_carryPw over a world relation R (a copy of its body with the journal and the kept relation at R; ps_carryPw is
   its instance at wle, ps_carryPw_R_wle): the bad escape's NULL return carries it at wle' segs RZ_cf *)
Definition ps_carryPwR (R : world segs -> world segs -> Prop) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B PST ARx R (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
Lemma ps_carryPw_R_wle : forall D ly S Hp W mem md k FPs WS,
  ps_carryPw D ly S Hp W mem md k FPs WS = ps_carryPwR (@wle segs) D ly S Hp W mem md k FPs WS.
Proof. reflexivity. Qed.
Definition ps_QP (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  ps_Q D ly' S' Hp' W' regs' mem' md' /\ P mem'.
Definition ps_postP (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  YCbqGwild.fpostW_xb (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D).
(* ps_postP over a world relation R (a copy of its body at YCbqGwild.fpostW_xbR; ps_postP is its instance at wle,
   ps_postP_R_wle) *)
Definition ps_postPR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) :
  world segs -> config -> Prop :=
  YCbqGwild.fpostW_xbR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D).
Lemma ps_postP_R_wle : forall CW D, ps_postP CW D = ps_postPR (@wle segs) CW D.
Proof. reflexivity. Qed.
(* a post at wle is the post at wle' segs RZ_cf (the journal's world conjunct, YA0nH.wle_wle') *)
Lemma ps_postP_lift : forall CW D W' c',
  ps_postP CW D W' c' -> ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D W' c'.
Proof.
intros CW D W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
exists ly', S', Hp', regs', mem', md', k, WS. split; [exact Hc|]. split; [exact HB|].
split; [exact (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
  (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)|].
split; [exact HX|]. split; [exact HP | exact HQ].
Qed.
(* THE HAND-OFF FORM: a stretch runs at wle (SRr, the engine's runners and call rules) into ps_finP, the SRr' fact of
   the stretch it hands its last state to; ps_finP_SRr' makes the whole an SRr' fact. A hand-off to a stretch that may
   cross the bad escape's fuzz_free is ps_finP_hand; to one that ends at wle (retok; ret0 before the free),
   ps_finP_of_postP. *)
Definition ps_finP (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Lemma ps_finP_SRr' : forall CW D W c, SRr segs W c (ps_finP CW D) ->
  SRr' segs YGcfRehidePost.RZ_cf W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros CW D W c H. exact (ps_SRr'_of_SRr W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) H).
Qed.
Lemma ps_finP_hand : forall CW D W c,
  SRr' segs YGcfRehidePost.RZ_cf W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) -> SRr segs W c (ps_finP CW D).
Proof.
intros CW D W c H. exact (ps_hand W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) H).
Qed.
Lemma ps_finP_of_postP : forall CW D W c, SRr segs W c (ps_postP CW D) -> SRr segs W c (ps_finP CW D).
Proof.
intros CW D W c H. eapply SRr_mono; [exact H|].
intros W' c' _ HQ. unfold ps_finP, SRr'.
apply (SRrG_ret segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf)).
exact (ps_postP_lift CW D W' c' HQ).
Qed.
(* a carry at budget [] is a budgeted carry within any cursor set (every cut but the bad escape's NULL return) *)
Lemma ps_carryPw_nil : forall CW D ly S Hp W mem md, (exists k, ps_carryP D ly S Hp W mem md k []) ->
  exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw D ly S Hp W mem md k [] WS.
Proof. intros CW D ly S Hp W mem md (k & H). exists k, []. split; [apply ps_wb_nil | exact H]. Qed.
Definition ps_at_scanP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
  ps_carryP D ly S Hp W mem md 0 [] /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  ly = pi_ly D /\ S = pi_S D /\ Hp = pi_Hp D /\ W = pi_W D /\
  LEDGER ly S Hp W mem (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 10 = w64 x /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 12 = w64 34 /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 20 = w64 (pi_p D + 1) /\
  pi_p D + 1 <= x < pi_text D + pi_len D /\
  PjGrammar.scan (ps_x D) =
    option_map (fun Q => (Q + Z.to_nat (x - (pi_p D + 1)))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) x)).
Definition ps_at_decP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  ps_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  ps_dec_rel D W mem out w r Q.
Definition ps_at_ret0P (CW : list (list Z)) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
(* ps_at_ret0P over a world relation R (its carry at R, ps_carryPwR; ps_at_ret0P is its instance at wle,
   ps_at_ret0P_R_wle) *)
Definition ps_at_ret0PR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) (ly : alayout)
  (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPwR R D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
Lemma ps_at_ret0P_R_wle : forall CW D ly S Hp W regs mem md,
  ps_at_ret0P CW D ly S Hp W regs mem md = ps_at_ret0PR (@wle segs) CW D ly S Hp W regs mem md.
Proof. reflexivity. Qed.
Definition ps_at_retokP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_sh_regs D regs /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  r = pi_p D + 1 + Z.of_nat Q /\
  (exists s, PjGrammar.decode (ps_x D) = Some (s, rest_atR (pi_tb D) (pi_text D) (r + 1)) /\
     bytes_at W mem out s /\ Z.of_nat (length s) = w - out) /\
  out <= w /\ w - out <= Z.of_nat Q.
Definition ps_seg_entryP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D, ps_pre CTX CW D -> P (pi_mem D) ->
  SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (SIGMA AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_scanP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md x, ps_pre CTX CW D -> ps_at_scanP D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_SCAN) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_decP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> ps_at_decP D ly S Hp W regs mem md out w r Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition ps_seg_ret0P (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0P CW D ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (ps_pc PS_RET0) regs mem md) (ps_postP CW D).
Definition ps_seg_ret0PR (R : world segs -> world segs -> Prop) (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0PR R CW D ly S Hp W regs mem md ->
  SRrG segs R W (cfg_at segs (ps_pc PS_RET0) regs mem md) (ps_postPR R CW D).
Lemma ps_seg_ret0P_R_wle : forall CTX CW, ps_seg_ret0P CTX CW = ps_seg_ret0PR (@wle segs) CTX CW.
Proof. reflexivity. Qed.
Definition ps_seg_retokP (CTX : list (list Z)) (CW : list (list Z)) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> ps_at_retokP D ly S Hp W regs mem md out w r Q ->
  SRr segs W (cfg_at segs (ps_pc PS_RETOK) regs mem md) (ps_postP CW D).
End gp.

(* ---- the stable statements are the P := (fun _ => True) instances, both ways ---- *)
Lemma ps_carryP_T : forall D ly S Hp W mem md k FPs,
  ps_carry D ly S Hp W mem md k FPs <-> ps_carryP (fun _ => True) D ly S Hp W mem md k FPs.
Proof.
intros. split; [intros (H1 & H2 & H3 & H4 & H5); exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I)))))|].
intros (H1 & H2 & H3 & H4 & H5 & _); exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma ps_ex_carryP_T : forall D ly S Hp W mem md,
  (exists k, ps_carry D ly S Hp W mem md k []) <-> (exists k, ps_carryP (fun _ => True) D ly S Hp W mem md k []).
Proof. intros. split; intros (k & H); exists k; apply ps_carryP_T; exact H. Qed.
Lemma ps_ex_carryPw_T : forall CW D ly S Hp W mem md,
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryw D ly S Hp W mem md k [] WS) <->
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw (fun _ => True) D ly S Hp W mem md k [] WS).
Proof.
intros. split; intros (k & WS & HB & H1 & H2 & H3 & H4 & H5); exists k, WS; split; try exact HB.
- exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I))))).
- destruct H5 as [H5 _]. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma ps_postP_T : forall CW D W' c', ps_postP (fun _ => True) CW D W' c' <-> ps_post CW D W' c'.
Proof.
intros CW D W' c'. split.
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & _).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP HQ))))).
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj HQ I)))))).
Qed.
Lemma ps_postPR_T : forall R CW D W' c', ps_postPR (fun _ => True) R CW D W' c' <-> ps_postR R CW D W' c'.
Proof.
intros R CW D W' c'. split.
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & _).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP HQ))))).
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj HQ I)))))).
Qed.
Lemma ps_ex_carryPwR_T : forall R CW D ly S Hp W mem md,
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carrywR R D ly S Hp W mem md k [] WS) <->
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPwR (fun _ => True) R D ly S Hp W mem md k [] WS).
Proof.
intros. split; intros (k & WS & HB & H1 & H2 & H3 & H4 & H5); exists k, WS; split; try exact HB.
- exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I))))).
- destruct H5 as [H5 _]. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Ltac ps_T_cut H := let Hc := fresh in
  first [ destruct H as (Hc & H); split; [apply ps_carryP_T; exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply ps_ex_carryP_T; exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply ps_ex_carryPw_T; exact Hc | exact H] ].
Ltac ps_T_cut_back H := let Hc := fresh in
  first [ destruct H as (Hc & H); split; [apply (proj2 (ps_carryP_T _ _ _ _ _ _ _ _ _)); exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply (proj2 (ps_ex_carryP_T _ _ _ _ _ _ _)); exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply (proj2 (ps_ex_carryPw_T _ _ _ _ _ _ _ _)); exact Hc | exact H] ].
Lemma ps_seg_entry_of_True : forall CTX CW, ps_seg_entryP (fun _ => True) CTX CW <-> ps_seg_entry CTX CW.
Proof.
intros CTX CW. split.
- intros H D HP. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP I)|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
- intros H D HP _. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP)|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.
Lemma ps_seg_scan_of_True : forall CTX CW, ps_seg_scanP (fun _ => True) CTX CW <-> ps_seg_scan CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md x HP HA. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md x HP); ps_T_cut HA|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
- intros H D ly S Hp W regs mem md x HP HA. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md x HP); ps_T_cut_back HA|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.
Lemma ps_seg_dec_of_True : forall CTX CW, ps_seg_decP (fun _ => True) CTX CW <-> ps_seg_dec CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md out w r Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [apply (H D ly S Hp W regs mem md out w r Q HP); ps_T_cut HA|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
- intros H D ly S Hp W regs mem md out w r Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out w r Q HP); ps_T_cut_back HA|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.
Lemma ps_seg_ret0_of_True : forall CTX CW, ps_seg_ret0P (fun _ => True) CTX CW <-> ps_seg_ret0 CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md HP HA. eapply SRr_mono; [apply (H D ly S Hp W regs mem md HP); ps_T_cut HA|].
  intros W' c' _ HQ. apply ps_postP_T. exact HQ.
- intros H D ly S Hp W regs mem md HP HA. eapply SRr_mono; [apply (H D ly S Hp W regs mem md HP); ps_T_cut_back HA|].
  intros W' c' _ HQ. apply ps_postP_T. exact HQ.
Qed.
Lemma ps_seg_ret0R_of_True : forall R CTX CW, ps_seg_ret0PR (fun _ => True) R CTX CW <-> ps_seg_ret0R R CTX CW.
Proof.
intros R CTX CW. split.
- intros H D ly S Hp W regs mem md HP (Hc & HA). eapply (SRrG_mono segs R);
    [apply (H D ly S Hp W regs mem md HP); split; [exact (proj1 (ps_ex_carryPwR_T R CW D ly S Hp W mem md) Hc) | exact HA]|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
- intros H D ly S Hp W regs mem md HP (Hc & HA). eapply (SRrG_mono segs R);
    [apply (H D ly S Hp W regs mem md HP); split; [exact (proj2 (ps_ex_carryPwR_T R CW D ly S Hp W mem md) Hc) | exact HA]|].
  intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.
Lemma ps_seg_retok_of_True : forall CTX CW, ps_seg_retokP (fun _ => True) CTX CW <-> ps_seg_retok CTX CW.
Proof.
intros CTX CW. split.
- intros H D ly S Hp W regs mem md out w r Q HP HA.
  eapply SRr_mono; [apply (H D ly S Hp W regs mem md out w r Q HP); ps_T_cut HA|].
  intros W' c' _ HQ. apply ps_postP_T. exact HQ.
- intros H D ly S Hp W regs mem md out w r Q HP HA.
  eapply SRr_mono; [apply (H D ly S Hp W regs mem md out w r Q HP); ps_T_cut_back HA|].
  intros W' c' _ HQ. apply ps_postP_T. exact HQ.
Qed.

(* ---- THE TOP'S STATEMENT IS THE KIT TEXT ITSELF: tparse_string_specX of the kit's cut 7cdbb61b5fa0 (PRH_FnReader.v
   f1ae32e3b2cd :517-681). Its binders are packed into one ps_in (mkPsIn), its premises are ps_pre (prh_cw_ok in the
   fifth conjunct, the wild room, the two live counts and the hull budget in the eighth), and its post fpostWbm ..
   (wbudget CW 0) .. is ps_postPR at wle' segs RZ_cf and P := ps_mn D with ps_Q's conjuncts put in the text's order (ps_postm_is_K0:
   ps_QP (ps_mn D) D gives fQmn (pi_mem D) (ps_QT D), and ps_QT's arms are ps_QresK, the text's verbatim). S4_PsTop
   applies ps_K0_of_entry to the composed entry stretch.
   The earlier statement is deleted, and the change from it was NOT a conversion: the kit's refused arm adds the
   outcome-exclusion conjunct (:624-629) and its ledger counts ((cnt + 1) mod 2 ^ 64) where the earlier statement had
   (cnt + 1); g_peak and g_ran_out are the earlier statement's. The walk proves both: the exclusion from fuzz_malloc's
   outcome clause (ps_excl_of_malloc), the mod
   from prh_alloc_post's refusal arm, which carries it. ---- *)
Lemma ps_postm_is_K0 : forall CW D W' c',
  ps_postPR (ps_mn D) (wle' segs YGcfRehidePost.RZ_cf) CW D W' c' ->
  fpostWbm B ARx SK (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)]
    (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QT D) W' c'.
Proof.
intros CW D W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & HMN).
exists ly', S', Hp', regs', mem', md', k, WS.
exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj (ps_QT_of_Q D ly' S' Hp' W' regs' mem' md' HQ) HMN)))))).
Qed.
Lemma ps_K0_of_entry : forall CTX CW,
  (forall D, ps_pre CTX CW D ->
     SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (SIGMA AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
       (ps_postPR (ps_mn D) (wle' segs YGcfRehidePost.RZ_cf) CW D)) ->
  tparse_string_specX B ARx SK CTX CW.
Proof.
intros CTX CW H. unfold tparse_string_specX.
intros most own ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran
  HPRE HUNIV HCH HCLOW HCW HGAP HROOM HWR HSEC H24 HHULL H10 HIN Hpl Hnth HWIN Hq1 Hq2 HRA HSRC HHOME HLED HCNT HLIVE.
pose (D := mkPsIn ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran most own).
(* the conjunction is built explicitly: `split` would also unfold fpre / fwin / src_rd, which are conjunctions *)
assert (HP : ps_pre CTX CW D)
  by exact (conj HPRE (conj HUNIV (conj HCH (conj HCLOW (conj HCW (conj HGAP (conj HROOM
    (conj (conj HWR (conj (conj HSEC H24) HHULL))
    (conj H10 (conj HIN (conj Hpl (conj Hnth (conj HWIN (conj Hq1 (conj Hq2 (conj HRA (conj HSRC (conj HHOME
    (conj HLED (conj HCNT HLIVE)))))))))))))))))))).
unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP)|].
intros W' c' _ HQ. exact (ps_postm_is_K0 CW D W' c' HQ).
Qed.

End ps.
