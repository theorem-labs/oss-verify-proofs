(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c: the walk's SHARED definitions, so its
   segments (PvB_A entry .. skip_ws, PvB_D dispatch and the short arms, PvB_N number arm, PvB_X exit) state their cuts
   over one vocabulary.
   - PvEnt bundles the entry values; pv_pre the entry premises (the union text lib/A/PRH_FnParse.v
     (sha256 ec73a628c44b; internal record): fpre, rd_pre, rd_room, the frames bound, the hull budget; rd_pre carries
     frm_zero); pv_Q the post (its content, with the ledger / blocks moves spelled out); pv_FINAL the entry's
     caller-window float post fpostWF_xbR at the footprint rd_fp q v, at the re-hiding relation; pv_FINK the
     continuation post (pv_FINAL in the record's relation YA0nH.SRr' segs RZ_cf).
   - pv_frame: what the prologue leaves and every cut keeps until the epilogue: the callee-saved values in the real
     frame, the fake-frame header, the fake frame's shadow bytes, the frame-base spill.
   Image facts enter as the B listing's atoms (VAL (A_OBJ i), BASE); no address literal. Numerals are frame offsets
   of the prologue (LENGTH: 160, 176, 64, 56, 48, -8 .. -104), the fake-frame header word the code stores (WORD: the
   frame magic 0x41b58ab3), its shadow bytes (WORD: 0xf1, 0xf8, 0xf3), the descriptor's offset in the read-only band
   (DERIVED: 38879 = B 0x197df - 0x10000) and listing offsets (DERIVED: B pc - 0x816cc). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Export PvB_Room.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* listing offsets of parse_value's cuts (DERIVED: B pc - B_prog_base 0x816cc) *)
Definition AF_pv : Z := 19632.        (* entry 0x8637c *)
Definition AF_pv_sm_ret : Z := 19748. (* after `jal __asan_stack_malloc_0`, 0x863f0 *)
Definition AF_pv_skw_ret : Z := 19896. (* after `jal skip_ws`, 0x86484 *)
Definition AF_pv_num : Z := 20172.    (* the number arm 0x86598: a0 = p, a1 = *p, a2 = end *)
Definition AF_pv_exit : Z := 20352.   (* the shared exit 0x8664c: s5 holds the result *)
Definition PV_MAGIC : Z := 1102416563.  (* 0x41b58ab3 *)
Definition PV_DESCR_OFF : Z := 38879.   (* the frame descriptor string, in the read-only band A_OBJ 2 *)
Definition pv_shadow_live : list Z := [241; 241; 241; 241; 248; 243; 243; 243].
(* the entry's ra and s0 .. s11: their slots below the entry sp and their register numbers *)
Definition pv_saved : list (Z * Z) :=
  [(-8, 1); (-16, 8); (-24, 9); (-32, 18); (-40, 19); (-48, 20); (-56, 21); (-64, 22); (-72, 23); (-80, 24);
   (-88, 25); (-96, 26); (-104, 27)].

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the entry values of one call; pe_most / pe_own are the two #102 ledger statics (alloc.c's g_most, fuzz_preset.c's
   g_own_ran_out: PRH_Base.v prh_glob's prh_most / prh_own), kept unchanged by the call, in the record's binder order
   (the batch kit, a working branch 240b06ed4fd4: lib/A/PRH_FnParse.v tparse_value_specX d CTX
   CTX0 CW; pe_CW is the cursor set CW of the wild-room form). The post-implication form has no run position at
   entry: the post quantifies it (PvB_Room.v rp_post). *)
Record PvEnt : Type := mkPvEnt {
  pe_ly : alayout; pe_S : astate; pe_Hp : list Z; pe_W : world SEGS; pe_regs : bvmap 5 word;
  pe_mem : word -> option byte; pe_md : Model; pe_ch : list (Z * Z * Z);
  pe_e : Z; pe_q : Z; pe_text : Z; pe_len : Z; pe_p : Z; pe_tb : list Z; pe_v : Z;
  pe_Lam : list (Z * Z); pe_peak : Z; pe_cnt : Z; pe_fail : Z; pe_ran : Z; pe_most : Z; pe_own : Z;
  pe_CTX : list (list Z); pe_CTX0 : list (list Z); pe_CW : list (list Z); pe_d : nat }.

Definition pe_rest (en : PvEnt) : list Z := rest_atR (pe_tb en) (pe_text en) (pe_p en).
Definition pe_gt (en : PvEnt) : list PjGrammar.ev := prhPv_gtrace (pe_d en) (pe_rest en).
Definition pe_STK (en : PvEnt) : Z := STK_parse_value (pe_d en).
Definition pe_FP (en : PvEnt) : list (Z * Z) :=
  [(pe_q en, pe_q en + 8); (pe_q en + 16, pe_q en + 20); (pe_v en, pe_v en + 56)].
Definition pe_sp (en : PvEnt) : Z := spZ (pe_regs en).

(* the entry premises: the record text's (PRH_FnParse.v tparse_value_specX d CTX CTX0 CW at the batch kit's tip 240b06ed4fd4),
   in this cut's order: the memory normal form (record premise 2) sits after the frames bound, the two live-count
   premises (the room's live list's peak sec / 24-byte-class counts along the model's grant-all trace), then the
   wild-room form's two (every cursor free trace at q is in CW, prh_cw_entry; the depot's wild part has room in CW,
   wild_room .. CW 0), and LAST the hull budget (:117-119; PRH_FnParse.v:326-327) *)
Definition pv_pre (en : PvEnt) : Prop :=
  fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en) (pe_ch en) /\
  In (raZ (pe_regs en) :: spine (pe_ch en)) (pe_CTX en) /\
  prh_univ_closure B (pe_CTX0 en) /\
  prh_cur_entry (pe_W en) (pe_mem en) (pe_regs en) (pe_q en) /\
  (exists ch', achain (pe_ly en) (aview SEGS (w_H (pe_W en)) (pe_mem en)) (spZ (pe_regs en)) (s0Z (pe_regs en)) ch' /\
     spine ch' = spine (pe_ch en)) /\
  ((pe_sp en <= pe_q en < pe_sp en + 16) \/
   (pe_sp en + 16 <= pe_q en /\
    exists ch', achain (pe_ly en) (aview SEGS (w_H (pe_W en)) (pe_mem en)) (spZ (pe_regs en))
      (prh_s0 F_parse_string (pe_q en)) ch')) /\
  getr (pe_regs en) 10 = w64 (pe_q en) /\ getr (pe_regs en) 11 = w64 (pe_v en) /\
  rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
    (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
    (pe_q en) (pe_text en)
    (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en) /\
  rd_room (pe_S en) (pe_gt en) /\
  Z.of_nat (length (frames (pe_S en))) + Z.of_nat (Nat.succ (PjGrammar.MAXD - pe_d en)) <= fs_frames 0 /\
  (* the entry memory's normal form (the form routed 09:46Z): what tparse_value_specX's pre
     carries after the text commit (requested 09:47Z); musl strtod's row needs it at the number arm's call *)
  YStrtodRowX.aj_memnorm SEGS (pe_mem en) /\
  (* the live-count premises (record premises 12 and 13), verbatim: the number arm's fuzz_malloc call reads its
     sec_cnt / ccnt24 bounds off them (PresetRun.pkR_prefix at j = 0, CfRoomLivePreset.v rs_live_blocks) *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pe_S en)))
    (PresetReqAt.rd_hevs (pe_gt en))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pe_S en)))
    (PresetReqAt.rd_hevs (pe_gt en))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  prh_cw_entry B (pe_CW en) (pe_W en) (pe_mem en) (pe_regs en) (pe_q en) /\
  YCbqGwild.wild_room (as_universe B) (pe_CW en) 0 (st_depot (pe_S en)) /\
  (* THE HULL BUDGET of the record text (its premise after the two live counts): room for the value's all-granted
     events; the one callee of each arm takes its own budget from it at the call state (pv_reader0's secs_same) *)
  PresetHullBudget.hull_budget (pe_S en) (PresetReqAt.rd_hevs (pe_gt en)).

(* THE OUTCOME of the record's post (the batch kit): on a model run that consumes the grant-all trace's events from the run
   position at entry (every allocation granted, none set to fail by the fail counter), the call keeps g_ran_out, its
   result and trace are the grant-all run's, and the position moves by them *)
Definition pv_outc (en : PvEnt) (res : option (PjTree.jv * list Z)) (tr : list PjGrammar.ev) (ran' : Z)
    (S' : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (pe_S en) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (pe_gt en)) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (pe_gt en))) ->
  (pe_fail en < pe_cnt en \/ pe_cnt en + Z.of_nat (PjGrammar.calls (pe_gt en)) <= pe_fail en) ->
  ran' = pe_ran en /\ fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) = (res, tr) /\
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (pe_gt en)))%nat H0 hist' S'.

(* THE FREE ORDER the record's post ties to the model (the batch kit): at every depth bound n from nlo, the tree's blocks D in
   pj_free's order F, whose sizes (plus the allocator head) are the model's frees of the value *)
Definition pv_ftie (en : PvEnt) (nlo : nat) (Lam' : list (Z * Z)) (W' : world SEGS) (mem' : word -> option byte)
    (D : list (Z * Z)) (ok : list bool) : Prop :=
  cf_head = PresetReqAt.HEAD -> forall n, (nlo <= n)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS (rdW W' mem') (prh_lin Lam') n (pe_v en) D F /\
      map (fun b => snd b + cf_head) F = prhPv_frees (pe_d en) (pe_rest en) ok.

(* THE OUTCOME OF AN INJECTED READING of the record's post (its conjunct after the outcome): at a model run whose next
   events are the value's under the model's grant list with the chosen failure at call fail - cnt, every allocation
   among them a consumer event, with the chosen failure inside the value's window, every failed outcome the call met
   is the chosen one *)
Definition pv_inj (en : PvEnt) (ok : list bool) (tr : list PjGrammar.ev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (pe_S en) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value prh_jr_strtod (pe_d en)
    (pe_rest en) (PresetReqAt.okk (Z.to_nat (pe_fail en - pe_cnt en))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value prh_jr_strtod
    (pe_d en) (pe_rest en) (PresetReqAt.okk (Z.to_nat (pe_fail en - pe_cnt en)))))))) ->
  pe_cnt en <= pe_fail en < pe_cnt en + Z.of_nat (PjGrammar.calls (pe_gt en)) ->
  PRH_Base.prh_granted ok (pe_cnt en) (pe_fail en) (PjGrammar.calls tr).

(* the post's memory part, with the frames clause a parameter fr and the result code a value: pv_Q below is it at
   fr := frames back to a permutation of the entry's and the code in a0; the exit cut states it at fr := the fake frame still
   frame still on top. In the record's order (the batch kit's tip 8ba304fe2f93): the ledger move is rd_ledger_move with g_most,
   the ledger move is rd_ledger_move with g_most, the grant-all trace and the refused peak; the blocks move is rd_blocks_move
   without its frames conjunct (that one is fr); the live room handed on is `blocks_bytes S' <= blocks_bytes S + prh_held tr`;
   the hull use after room_live_cf S' (the record's hull_used over the value's all-granted events); the room post is the
   record's two conjuncts after it (PvB_Room.v rp_post), then the outcome (pv_outc) and the outcome of an injected reading
   (pv_inj); the ledger statics most / own are the entry's; each result arm carries the free-order tie (pv_ftie), the success
   arm the node's capacity words (pj_ncapR). Read it through pvQ_R below, never by a positional destruct. *)
Definition pv_Qm (en : PvEnt) (fr : astate -> Prop) (code : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world SEGS) (mem' : word -> option byte) : Prop :=
  exists (ok : list bool) res tr okr D Lam' peak' cnt' fail' ran',
  PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok = (res, tr, okr) /\
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' (pe_most en) (pe_own en) /\ room_live_cf S' /\
  PresetHullBudget.hull_used (pe_S en) S' (PresetReqAt.rd_hevs (pe_gt en)) /\
  rp_post tr (pe_S en) S' /\
  pv_outc en res tr ran' S' /\
  pv_inj en ok tr /\
  rd_ledger_move (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) ok (pe_gt en) tr D Lam'
    peak' cnt' fail' ran' /\
  (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B (pe_ly en) (pe_S en))) /\
  Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B (pe_ly en) (pe_S en)) /\
  fr S' /\
  hpeakR tr <= 224 * Z.of_nat (length (pe_rest en)) + 512 * Z.of_nat (PjGrammar.MAXD - pe_d en) /\
  blocks_bytes S' <= blocks_bytes (pe_S en) + prh_held tr /\
  Ledger.lsum D = PjGrammar.held tr /\
  match res with
  | Some (t, r) =>
      code = 0 /\
      pv_ftie en (PjTree.depth t) Lam' W' mem' D ok /\
      pj_in_okR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en) (pe_text en + pe_len en - Z.of_nat (length r))
        (Z.of_nat (pe_d en)) (pe_tb en) /\
      pj_nodeR SEGS (rdW W' mem') (prh_lin Lam') (pe_v en) t D /\
      pj_ncapR SEGS (rdW W' mem') (pe_v en) t /\
      Ledger.lsum D <= 224 * (Z.of_nat (length (pe_rest en)) - Z.of_nat (length r))
  | None =>
      code = -1 /\
      pv_ftie en (PjGrammar.MAXD - pe_d en) Lam' W' mem' D ok /\
      pj_in_afterR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en) (Z.of_nat (pe_d en)) 33 /\
      pj_fdR SEGS (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - pe_d en) (pe_v en) D
  end.

Local Set Implicit Arguments.
(* pv_Qm's conjuncts BY NAME: pvQ_R_of reads pv_Qm into the record, pvQ_of_R builds pv_Qm from it, so a consumer is not
   broken by the next conjunct *)
Record pvQ_R (en : PvEnt) (fr : astate -> Prop) (code : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world SEGS) (mem' : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z))
    (tr : list PjGrammar.ev) (okr : list bool) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop := {
  pvq_run : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok = (res, tr, okr);
  pvq_ledger : prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' (pe_most en) (pe_own en);
  pvq_room : room_live_cf S';
  pvq_hull : PresetHullBudget.hull_used (pe_S en) S' (PresetReqAt.rd_hevs (pe_gt en));
  pvq_rp : rp_post tr (pe_S en) S';
  pvq_outc : pv_outc en res tr ran' S';
  pvq_inj : pv_inj en ok tr;
  pvq_move : rd_ledger_move (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) ok (pe_gt en)
    tr D Lam' peak' cnt' fail' ran';
  pvq_fresh : forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B (pe_ly en) (pe_S en));
  pvq_perm : Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B (pe_ly en) (pe_S en));
  pvq_fr : fr S';
  pvq_peak : hpeakR tr <= 224 * Z.of_nat (length (pe_rest en)) + 512 * Z.of_nat (PjGrammar.MAXD - pe_d en);
  pvq_bytes : blocks_bytes S' <= blocks_bytes (pe_S en) + prh_held tr;
  pvq_lsum : Ledger.lsum D = PjGrammar.held tr;
  pvq_arm : match res with
    | Some (t, r) =>
        code = 0 /\
        pv_ftie en (PjTree.depth t) Lam' W' mem' D ok /\
        pj_in_okR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en) (pe_text en + pe_len en - Z.of_nat (length r))
          (Z.of_nat (pe_d en)) (pe_tb en) /\
        pj_nodeR SEGS (rdW W' mem') (prh_lin Lam') (pe_v en) t D /\
        pj_ncapR SEGS (rdW W' mem') (pe_v en) t /\
        Ledger.lsum D <= 224 * (Z.of_nat (length (pe_rest en)) - Z.of_nat (length r))
    | None =>
        code = -1 /\
        pv_ftie en (PjGrammar.MAXD - pe_d en) Lam' W' mem' D ok /\
        pj_in_afterR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en) (Z.of_nat (pe_d en)) 33 /\
        pj_fdR SEGS (rdW W' mem') (prh_lin Lam') (PjGrammar.MAXD - pe_d en) (pe_v en) D
    end }.

Lemma pvQ_R_of : forall en fr code ly' S' Hp' W' mem', pv_Qm en fr code ly' S' Hp' W' mem' ->
  exists ok res tr okr D Lam' peak' cnt' fail' ran',
    pvQ_R en fr code ly' S' Hp' W' mem' ok res tr okr D Lam' peak' cnt' fail' ran'.
Proof.
intros en fr code ly' S' Hp' W' mem' (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & H1 & H2 & H3 &
  H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
exact {| pvq_run := H1; pvq_ledger := H2; pvq_room := H3; pvq_hull := H4; pvq_rp := H5; pvq_outc := H6;
  pvq_inj := H7; pvq_move := H8; pvq_fresh := H9; pvq_perm := H10; pvq_fr := H11; pvq_peak := H12; pvq_bytes := H13;
  pvq_lsum := H14; pvq_arm := H15 |}.
Qed.

Lemma pvQ_of_R : forall en fr code ly' S' Hp' W' mem' ok res tr okr D Lam' peak' cnt' fail' ran',
  pvQ_R en fr code ly' S' Hp' W' mem' ok res tr okr D Lam' peak' cnt' fail' ran' ->
  pv_Qm en fr code ly' S' Hp' W' mem'.
Proof.
intros en fr code ly' S' Hp' W' mem' ok res tr okr D Lam' peak' cnt' fail' ran' HR.
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
exact (conj (pvq_run HR) (conj (pvq_ledger HR) (conj (pvq_room HR) (conj (pvq_hull HR) (conj (pvq_rp HR)
  (conj (pvq_outc HR) (conj (pvq_inj HR) (conj (pvq_move HR) (conj (pvq_fresh HR) (conj (pvq_perm HR)
  (conj (pvq_fr HR) (conj (pvq_peak HR) (conj (pvq_bytes HR) (conj (pvq_lsum HR) (pvq_arm HR))))))))))))))).
Qed.
Local Unset Implicit Arguments.

(* the outcome across a step with no model event after the call (the exit's release: rp_keep_stack_free) *)
Lemma pv_outc_keep : forall en res tr ran' S1 S2, pv_outc en res tr ran' S1 -> rp_keep S1 S2 ->
  pv_outc en res tr ran' S2.
Proof.
intros en res tr ran' S1 S2 H [_ K] sm x os i H0 hist P R C F.
destruct (H sm x os i H0 hist P R C F) as (E1 & E2 & h & P1).
split; [exact E1|]. split; [exact E2|]. exact (K _ _ _ _ _ _ P1).
Qed.

(* the outcome of an arm with no allocator call (p >= end, a literal): the grant-all run makes no event, the ledger's
   g_ran_out is the entry's, the run is the grant-all run (the arm reads no outcome), the position is kept *)
Lemma pv_outc_nil : forall en res tr S', PresetReqAt.rd_hevs (pe_gt en) = [] ->
  fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) = (res, tr) -> rp_keep (pe_S en) S' ->
  pv_outc en res tr (pe_ran en) S'.
Proof.
intros en res tr S' E Ej [_ K] sm x os i H0 hist P _ _ _.
split; [reflexivity|]. split; [exact Ej|].
rewrite E. cbn [length]. rewrite Nat.add_0_r. exact (K _ _ _ _ _ _ P).
Qed.

(* the outcome of an arm with ONE call that makes model events (string, number, container): the callee's outcome at
   the call state Sc over the value's grant-all events evs, the room kept from entry to Sc and from the callee's
   post state Sc' to S' *)
Lemma pv_outc_call : forall en res tr ran' Sc Sc' S' (evs : list PresetReqAt.hev),
  PresetReqAt.rd_hevs (pe_gt en) = evs -> rp_keep (pe_S en) Sc ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> PRH_Base.prh_run_at sm x os i evs ->
     PRH_Base.prh_cons_from sm x os i (length evs) ->
     (pe_fail en < pe_cnt en \/ pe_cnt en + Z.of_nat (PjGrammar.calls (pe_gt en)) <= pe_fail en) ->
     ran' = pe_ran en /\ fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) = (res, tr) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length evs)%nat H0 hist' Sc') ->
  rp_keep Sc' S' -> pv_outc en res tr ran' S'.
Proof.
intros en res tr ran' Sc Sc' S' evs E [_ K1] HC [_ K2] sm x os i H0 hist P R C F.
rewrite E in R, C |- *. destruct (K1 _ _ _ _ _ _ P) as [h1 P1].
destruct (HC sm x os i H0 h1 P1 R C F) as (E1 & E2 & h2 & P2).
split; [exact E1|]. split; [exact E2|]. exact (K2 _ _ _ _ _ _ P2).
Qed.

(* ---- The batch kit's per-event live room (rd_room's third conjunct, PRH_FnParse.v at 03fcabb582d0: prh_live_evs S (rd_hevs gt),
   PRH_Base.v prh_live_at / prh_ev_req) ---- *)

(* the allocator's live bytes are the room's live list summed *)
Lemma pv_bb_live : forall s : astate, blocks_bytes s = fold_right Z.add 0 (map snd (blocks s)).
Proof.
intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k l IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc k);
  [cbn [map fold_right snd]; rewrite IH; reflexivity | exact IH].
Qed.

(* the per-event live room across a step that keeps the live list (the C1 / N call states: pv_reader0's rp_keep) *)
Lemma pv_live_evs_keep : forall S Sc E, prh_live_evs S E -> rp_keep S Sc -> prh_live_evs Sc E.
Proof.
intros S Sc E H [L _] j e Hj. unfold prh_live_at. rewrite L. exact (H j e Hj).
Qed.

Lemma rd_room_keep : forall S Sc gt, rd_room S gt -> rp_keep S Sc -> room_live_cf Sc -> rd_room Sc gt.
Proof.
intros S Sc gt (_ & H2 & H3) K R. split; [exact R|]. split; [exact H2|]. exact (pv_live_evs_keep S Sc _ H3 K).
Qed.

(* the first event's request fits the live room on top of the allocator's live bytes (j = 0) *)
Lemma pv_live_first : forall S (E : list PresetReqAt.hev) e E', prh_live_evs S E -> E = e :: E' ->
  blocks_bytes S + prh_ev_req e <= LIVE_MAX.
Proof.
intros S E e E' H ->. pose proof (H 0%nat e eq_refl) as H0. unfold prh_live_at in H0.
cbn [firstn PresetReqAt.hlive_from fold_left] in H0.
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in H0.
rewrite pv_bb_live. exact H0.
Qed.

Lemma rd_room_first : forall S gt e E', rd_room S gt -> PresetReqAt.rd_hevs gt = e :: E' ->
  blocks_bytes S + prh_ev_req e <= LIVE_MAX.
Proof. intros S gt e E' (_ & _ & H3) E. exact (pv_live_first S _ e E' H3 E). Qed.

(* the post: the memory part with frames back to a permutation of the entry's and the code in a0, and the memory normal
   form at the exit memory (the record's fpostWFbm keep `memnorm mem -> memnorm mem'` follows, the entry's memnorm
   being pv_pre's) *)
Definition pv_Q (en : PvEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) ->
    Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' => (exists code, getr regs' 10 = w64 code /\
    pv_Qm en (fun S2 => Permutation (frames S2) (frames (pe_S en))) code ly' S' Hp' W' mem') /\
    YAkMemnorm.memnorm SEGS mem'.

(* the entry's post, at the entry float state fx0: the batch kit's budgeted caller-window post fpostWF_xbR at the wild budget
   wbudget CW 0, with its journal at the re-hiding relation wle' segs RZ_cf (the record's fpostWFbm, lib/A/PRH_Base.v
   fpostWFb, which is fpostWF_xbR at wle' segs RZ_cf: the run crosses parse_items / parse_string, which free) *)
Definition pv_FINAL (en : PvEnt) : world SEGS -> config -> Prop :=
  @YCbqGwild.fpostWF_xbR fx0 rc SK SEGS B (@prh_pst prh_img_B) ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (YCbqGwild.wbudget (pe_CW en) 0) (pe_STK en) (pe_e en) (pe_FP en) (pe_regs en) (pe_ly en) (pe_S en) (pe_Hp en)
    (pe_W en) (pe_mem en) (pe_md en) (pv_Q en).

(* the continuation post of the segments that call no freeing function (entry .. C1, the dispatch and the literal arm,
   the number arm): their runs stay plain SRr, and each continuation reaches the final post in the record's relation
   (YA0nH.SRr' segs RZ_cf); YGcfRhLift.ra_rh_of_SRr lifts such a run once *)
Definition pv_FINK (en : PvEnt) : world SEGS -> config -> Prop :=
  fun W c => YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W c (pv_FINAL en).

(* ---- the frame parse_value keeps from the end of its prologue to its exit ---- *)
(* sp0: the entry sp (s0); Y: the realigned sp (s1 = sp), sp0 - 176 <= Y <= sp0 - 160, Y = 0 (mod 32); fa: the fake
   frame (s2 = s10), a live class-0 frame, fl its flag cell (the runtime's word at fa + 56). The real frame holds the
   entry's ra and s0 .. s11 at sp0 - 8 .. sp0 - 104, and fa at Y + 48; the fake frame's header is the magic, the frame
   descriptor and parse_value's pc; its 8 shadow bytes are shb (pv_shadow_live after the prologue; the number arm
   clears byte 4, the end-pointer slot, while it owns it). The prologue's `sd zero, 0(sp)` at sp0 - 160 is a stack
   probe: no cut states it, because the body spills through s1 = Y at Y .. Y + 31 (0x86714, 0x86780, 0x867a4, 0x867a8),
   which covers sp0 - 160 in both alignments, and the epilogue (0x866b0 .. 0x866ec) never reads it. *)
Definition pv_frame (regs0 : bvmap 5 word) (sp0 Y fa fl : Z) (shb : list Z) (W : world SEGS)
    (mem : word -> option byte) : Prop :=
  sp0 - 176 <= Y <= sp0 - 160 /\ Y mod 32 = 0 /\
  (forall a, Y <= a < sp0 -> apresent (w_H W) mem a) /\
  Forall (fun oc => val_mem SEGS (rdW W mem) (sp0 + fst oc) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 (snd oc)))))
    pv_saved /\
  val_mem SEGS (rdW W mem) (Y + 48) 8 fa /\
  val_mem SEGS (rdW W mem) fa 8 PV_MAGIC /\
  val_mem SEGS (rdW W mem) (fa + 8) 8 (VAL (A_OBJ 2) + PV_DESCR_OFF) /\
  val_mem SEGS (rdW W mem) (fa + 16) 8 (BASE + AF_pv) /\
  val_mem SEGS (rdW W mem) (fa + 56) 8 fl /\
  (forall a, fa <= a < fa + 64 -> apresent (w_H W) mem a) /\
  length shb = 8%nat /\
  garr8 SEGS (rdW W mem) (SHADOW_OFF + fa / 8) shb.

(* the registers the body keeps from the prologue to the exit *)
Definition pv_keep_regs (en : PvEnt) (regs : bvmap 5 word) (Y fa : Z) : Prop :=
  getr regs 2 = w64 Y /\ getr regs 8 = w64 (pe_sp en) /\ getr regs 18 = w64 fa /\ getr regs 26 = w64 fa /\
  getr regs 27 = w64 (SHADOW_OFF + fa / 8) /\ getr regs 23 = w64 SHADOW_OFF /\
  getr regs 3 = getr (pe_regs en) 3 /\ getr regs 4 = getr (pe_regs en) 4.

(* the state every body cut shares: the frame, the journal from entry (widened by the window, own = the fake frame),
   the window kept *)
Definition pv_body (en : PvEnt) (Y fa fl pos : Z) (shb : list Z) (lyc : alayout) (Sc : astate) (Hpc : list Z)
    (W' : world SEGS) (mem : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  pv_frame (pe_regs en) (pe_sp en) Y fa fl shb W' mem /\
  In (0, pos) (frames Sc) /\ fa = frame_addr lyc 0 pos /\ fl = flag_addr lyc 0 pos /\
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k /\
  (forall a, pe_sp en <= a < pe_sp en + pe_e en -> ~ inFP (pe_FP en) a ->
     aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a).

(* the body at the EXIT cut: the journal is budgeted (YCbqG.ajournal_xwR over the wild traces WS the string / container
   call added), WS within the cursor set CW (wbudget CW 0), and at the re-hiding relation wle' segs RZ_cf (the string
   and container calls free); at C1 and N the journal is ajournal_x (WS = [], wle) *)
Definition pv_body_w (en : PvEnt) (Y fa fl pos : Z) (shb : list Z) (lyc : alayout) (Sc : astate) (Hpc : list Z)
    (W' : world SEGS) (mem : word -> option byte) (mdc : Model) (k : Z) (WS : list (list Z)) : Prop :=
  pv_frame (pe_regs en) (pe_sp en) Y fa fl shb W' mem /\
  In (0, pos) (frames Sc) /\ fa = frame_addr lyc 0 pos /\ fl = flag_addr lyc 0 pos /\
  ajournal_xwR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k WS /\
  (forall a, pe_sp en <= a < pe_sp en + pe_e en -> ~ inFP (pe_FP en) a ->
     aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a).

Definition pv_body_x (en : PvEnt) (Y fa fl pos : Z) (shb : list Z) (lyc : alayout) (Sc : astate) (Hpc : list Z)
    (W' : world SEGS) (mem : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  exists WS, pv_body_w en Y fa fl pos shb lyc Sc Hpc W' mem mdc k WS /\ YCbqGwild.wbudget (pe_CW en) 0 WS.

(* an unbudgeted body (no wild trace since entry, the journal at wle) is a budgeted one at WS = [], its journal lifted
   to wle' segs RZ_cf (YA0nH.wle_wle') *)
Lemma pv_body_x_of : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k,
  pv_body en Y fa fl pos shb lyc Sc Hpc W' mem mdc k -> pv_body_x en Y fa fl pos shb lyc Sc Hpc W' mem mdc k.
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k (HF & HI & Ea & El & HJ & HW). exists [].
split; [split; [exact HF|]; split; [exact HI|]; split; [exact Ea|]; split; [exact El|]; split; [|exact HW]|].
- eapply (ajournal_xwR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS));
    [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ].
- unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. apply Nat.le_refl.
Qed.

(* what the reader's state is before any allocation: the allocator state is the entry's with the fake frame on top,
   the node, the text and the ledger as at entry, the cursor at p1 *)
Definition pv_reader0 (en : PvEnt) (pos p1 : Z) (lyc : alayout) (Sc : astate) (W' : world SEGS)
    (mem : word -> option byte) : Prop :=
  frames Sc = (0, pos) :: frames (pe_S en) /\ ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) /\
  blocks_bytes Sc = blocks_bytes (pe_S en) /\
  rd_room Sc (pe_gt en) /\
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) /\
  src_rd W' mem (pe_text en) (pe_tb en) /\ prhReader_home B lyc Sc (pe_Hp en) (pe_Lam en) (pe_text en) (pe_len en) /\
  (forall a, pe_v en <= a < pe_v en + 56 -> aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF (pe_v en) 56 /\
  prh_ledger B lyc Sc (pe_Hp en) W' mem (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
    (pe_own en) /\
  (* the room, unmoved since entry: no allocator step before the number arm's call (the live list equal, the run
     position kept; PvB_Room.v rp_keep) *)
  rp_keep (pe_S en) Sc /\
  (* the hull meters, unmoved since entry (the fake-frame take is a set_fs): the one callee's hull budget at the call
     state is pv_pre's, and the arm's hull use from the entry is the callee's *)
  YGcfSecsStep.secs_same (pe_S en) Sc.

(* the call chain every call of the body needs (aj_call_xW / aj_call_xWbR / aj_call_xWFbR: the callee's fpre reads a
   chain from the caller's sp at s0 = sp0): through parse_value's OWN frame record (saved s0 / ra at sp0 - 16 / sp0 - 8,
   written by the prologue) and then the caller's chain, at the cut's memory and under any view that agrees with it
   outside the node's type word (segment D writes only that word before its calls; segment D's request, 06:4xZ) *)
Definition pv_chain (en : PvEnt) (lyc : alayout) (W' : world SEGS) (mem : word -> option byte) (Y : Z) : Prop :=
  forall rd', (forall a, ~ (pe_v en <= a < pe_v en + 4) -> rd' a = aview SEGS (w_H W') mem a) ->
    exists ch1, achain lyc rd' Y (pe_sp en) ch1.

(* C1: back from skip_ws (B 0x86484); the cursor is past the white space. The last conjunct carries the memory normal
   form from the entry to the number arm's strtod call (owner 10:2xZ: C1 and N carry it, the exit cut does not) *)
Definition pv_at_C1 (en : PvEnt) (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists regs mem Y fa fl pos lyc Sc k,
  ms = @YK11.mkst fx0 regs (Z_to_bv 64 (BASE + AF_pv_skw_ret)) mem (YK11.seg_rom SEGS) /\
  pv_keep_regs en regs Y fa /\ getr regs 9 = w64 Y /\ getr regs 19 = w64 (pe_v en) /\ getr regs 20 = w64 (pe_q en) /\
  pv_body en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_chain en lyc W' mem Y /\
  pv_reader0 en pos (pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en)))) lyc Sc W' mem /\
  YStrtodRowX.aj_memnorm SEGS mem.

(* N: the number arm (B 0x86598), reached from the dispatch: the first byte c after the white space is none of
   the six dispatch bytes (brace, bracket, double quote, t, f, n); a0 = its address p1, a1 = c, a2 = end, s8 = q's
   shadow address; otherwise as C1 *)
Definition pv_at_N (en : PvEnt) (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists regs mem Y fa fl pos lyc Sc k c y,
  ms = @YK11.mkst fx0 regs (Z_to_bv 64 (BASE + AF_pv_num)) mem (YK11.seg_rom SEGS) /\
  pv_keep_regs en regs Y fa /\ getr regs 9 = w64 Y /\ getr regs 19 = w64 (pe_v en) /\ getr regs 20 = w64 (pe_q en) /\
  getr regs 24 = w64 (SHADOW_OFF + pe_q en / 8) /\
  PjGrammar.skip (pe_rest en) = c :: y /\
  getr regs 10 = w64 (pe_text en + pe_len en - Z.of_nat (length (c :: y))) /\ getr regs 11 = w64 c /\
  getr regs 12 = w64 (pe_text en + pe_len en) /\
  c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110 /\
  pv_body en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_chain en lyc W' mem Y /\
  pv_reader0 en pos (pe_text en + pe_len en - Z.of_nat (length (c :: y))) lyc Sc W' mem /\
  YStrtodRowX.aj_memnorm SEGS mem.

(* EXIT: at the shared exit (B 0x8664c) with the result code in s5, the fake frame still on top (its shadow back to
   pv_shadow_live), the float state any with the rounding mode 0 and fs0 - fs11 kept, the post's memory part holding
   with the frames clause `the fake frame on top of a permutation of the entry's frames` (its run position inside
   pv_Qm, keyed on the trace), and the memory normal form at the exit memory, its last conjunct *)
Definition pv_at_exit (en : PvEnt) (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists (fx' : YK11.FPState) regs mem Y fa fl pos lyc Sc Hpc k code,
  ms = @YK11.mkst fx' regs (Z_to_bv 64 (BASE + AF_pv_exit)) mem (YK11.seg_rom SEGS) /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx0 fx' /\
  pv_keep_regs en regs Y fa /\ getr regs 21 = w64 code /\
  pv_body_x en Y fa fl pos pv_shadow_live lyc Sc Hpc W' mem mdc k /\
  pv_Qm en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) code lyc Sc Hpc W' mem /\
  YAkMemnorm.memnorm SEGS mem.

End c.
