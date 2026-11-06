(* write_value's CONTAINER arms, fs.asan image A: the item loop's invariant.
   The arm's run is a chain of program calls (put of '[' / '{', indent, per item put_string of the key, put of the
   separator, write_value of the item, put of ',', the closing indent, and the TAIL put of ']' / '}'). Between two
   calls the walk holds this invariant: the engine state at the resume point (ZZwv_defs' wvc_ssL), the caller's
   journal over the unpoisoned memory, and the writer facts the next callee's contract asks for, all against the
   model state WriterApp.putN of the pieces written so far.
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0): write_value has RELEASED proofs for fs's PLAIN
   and UBSAN builds only (lib/Prog, lib/U/Prog), none for ASan; they are templates, not drop-ins. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_writer_tbl FSH_Fn_writer ZZwv_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the arm's FIXED data: what the entry fixes and no call changes ---- *)
Record wvc_fix : Type := mkWF {
  wf_ty : Z; wf_p : Z; wf_d : Z;                       (* the node's type, the pretty flag, the depth *)
  wf_ot : Z; wf_o : Z; wf_v : Z;                       (* the window top, the out-object, the node *)
  wf_str : Z; wf_kids : Z; wf_keys : Z; wf_n : Z;      (* the node's fields *)
  wf_buf0 : Z; wf_cap0 : Z; wf_failed0 : Z;            (* the out-object at the arm's entry *)
  wf_text0 : list Z; wf_live : Z; wf_peak0 : Z; wf_cnt0 : Z; wf_fail0 : Z;
  wf_UL : list (Z * Z); wf_D : list (Z * Z);           (* the tree's reader blocks *)
  wf_t : PjTree.jv;                                    (* the tree the arm writes *)
  wf_ra8 : Z;                                          (* the word at o - 8, which every callee keeps *)
  wf_sp : Z;                                           (* write_value's entry sp: its frame is [sp - WVC_F, sp) *)
  wf_m : nat }.                                        (* the stack level 2 - k of write_value_spec_at k *)
(* the model state after the pieces written so far *)
Definition wvc_st0 (F : wvc_fix) : WriterApp.wst :=
  WriterApp.mkW (wf_failed0 F) (wf_text0 F) (wf_cap0 F) (wf_cnt0 F) (wf_fail0 F) [].
Definition wvc_stP (F : wvc_fix) (P : list (list Z)) : WriterApp.wst := WriterApp.putN (wvc_st0 F) P.
(* the caller's journal: from the entry, with the RAISED window top ot (FSH_Fn_writer.wpost), over the footprint the
   spec's post names (the statics and the entry buffer) *)
Definition wvc_STK (F : wvc_fix) : Z := STK_write_value (wf_m F) + (wf_ot F - wf_sp F).
Definition wvc_FP (F : wvc_fix) : list (Z * Z) := FS_PSTAT_FP ++ wbuf_fp (wf_buf0 F) (wf_cap0 F).

(* ---- the writer facts at a point of the walk, against the model state st and the live buffer buf ----
   The window of wkeep starts at the ENTRY sp: write_value's own frame [sp - WVC_F, sp) is below it, so the runs between
   calls keep it, and each callee's wkeep (from its own sp = sp - WVC_F) is weakened to it (ZZwv_comp.wv_wkeep_mono).
   The chain facts at o are the entry's one-node clause: case 1 (o = sp + 8, write_value called from pj_write) needs
   no memory fact (the word at o - 16 is write_value's own saved-ra slot, read from the frame at each call); case 2
   keeps both words, which lie in [sp, o) and so are kept by every run and every callee. *)
Definition wvc_sem (F : wvc_fix) (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (U : list (Z * Z))
    (W : world tfibsegs) (mem : word -> option byte) (buf : Z) (st : WriterApp.wst) : Prop :=
  wout_ok B tfibsegs ly S W mem (wf_o F) buf (WriterApp.w_cap st) (WriterApp.w_failed st) (WriterApp.w_text st) /\
  (exists peak, wf_peak0 F <= peak <= Z.max (wf_peak0 F) (wf_live F - wf_cap0 F + WriterApp.w_cap st) /\
     fs_glob tfibsegs W mem (wf_live F + WriterApp.w_cap st - wf_cap0 F) peak
       (WriterApp.w_cnt st) (WriterApp.w_fail st)) /\
  fs_heads B ly S U /\
  uswap U0 U (wf_buf0 F) buf (wf_cap0 F) /\
  bswap (ablocks B ly0 S0) (ablocks B ly S) (wf_buf0 F) buf (wf_cap0 F) (WriterApp.w_cap st) /\
  wbudget_kept S0 S (wf_failed0 F) (wf_cap0 F) (wf_cnt0 F)
    (WriterApp.w_failed st) (WriterApp.w_cap st) (WriterApp.w_cnt st) /\
  WriterApp.w_cnt st = wf_cnt0 F + wcalls st /\
  wkeep tfibsegs W0 W mem0 mem (wf_sp F) (wf_ot F) (wf_o F) 32 /\
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) (wf_UL F)) (wf_v F) (wf_t F) (wf_D F) /\
  FSH_Fn_reader.pobj tfibsegs B ly S W mem (wf_v F) /\
  (* the node's 56 bytes are the entry's (its header fields are the walk's atoms) *)
  (forall x : word, wf_v F <= bv_unsigned x < wf_v F + 56 -> rdW W mem x = rdW W0 mem0 x) /\
  (* the tree's OWN blocks stay live reader blocks (UL may also hold the writer's buffer, which a put frees) *)
  ublocks_ok B tfibsegs ly S W mem (wf_D F) /\
  (forall a k, In (a, k) (wf_D F) -> In (a, k) (wf_UL F) /\ a <> buf) /\
  (WriterApp.w_cap st <> 0 -> wf_v F + 56 <= buf - HEAD \/ buf + WriterApp.w_cap st <= wf_v F) /\
  (WriterApp.w_cap st <> 0 -> In (buf - HEAD, WriterApp.w_cap st + HEAD) (ablocks B ly S)) /\
  (WriterApp.w_cap st = 0 -> buf = 0) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) /\
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) (wf_o F - 8) = Some (wf_ra8 F) /\
  ((wf_o F = wf_sp F + 8 /\ raZ regs0 < alloc_ceiling) \/
   (wf_sp F + 16 <= wf_o F /\
    exists nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (wf_o F - 16) = Some nfp /\
      (wf_ra8 F < 4096 \/ nfp < alloc_ceiling))) /\
  (* the live buffer's head is user-poisoned (the writer specs' `cap <> 0 -> In (buf - HEAD, HEAD) U`) *)
  (WriterApp.w_cap st <> 0 -> In (buf - HEAD, HEAD) U).

(* ---- the invariant at a LOOP resume point r, after the pieces P, at item i (ke = the key slot keys + 8 * i, key =
   the key pointer read from it for an object, 0 for an array) ---- *)
Definition wvc_inv (F : wvc_fix) (r i ke key : Z) (P : list (list Z))
    (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
    (md0 : Model) (regs0 : bvmap 5 word)
    (W : world tfibsegs) (ms : machine_state) (mdc : Model)
    (ly : alayout) (S : astate) (U : list (Z * Z)) (buf : Z) : Prop :=
  let st := wvc_stP F P in
  let E := Ereg (ms_regs ms)
             (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) ke key) in
  wvc_at B E (wvc_ssL (wf_ty F) (wf_p F) r) (wvc_SHL (wf_ty F)) W ms (wvc_STK F) (wf_ot F) (wvc_FP F)
    ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U mdc (wevk (wf_cap0 F) st) /\
  wvc_sem F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st /\
  (* the loop's registers, and the atoms the env pins *)
  YK11.getr (ms_regs ms) 8%bv = w64 (wf_o F) /\
  YK11.getr (ms_regs ms) 9%bv = w64 (wf_v F) /\
  YK11.getr (ms_regs ms) 19%bv = w64 (wf_p F) /\
  YK11.getr (ms_regs ms) 21%bv = w64 i /\
  YK11.getr (ms_regs ms) 25%bv = w64 (56 * i) /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs0 3%bv /\
  YK11.getr (ms_regs ms) 4%bv = YK11.getr regs0 4%bv /\
  (* the loop state's other registers, as values (wvc_ssL names them symbolically) *)
  YK11.getr (ms_regs ms) 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) /\
  YK11.getr (ms_regs ms) 20%bv = w64 (wf_v F + 40) /\
  YK11.getr (ms_regs ms) 22%bv = w64 (8 * i) /\
  YK11.getr (ms_regs ms) 23%bv = w64 (wf_v F + 24) /\
  YK11.getr (ms_regs ms) 24%bv = w64 (wf_d F + 1) /\
  YK11.getr (ms_regs ms) 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) /\
  YK11.getr (ms_regs ms) 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) /\
  spZ (ms_regs ms) = wf_sp F - WVC_F /\
  0 <= i < wf_n F /\ ke = wf_keys F + 8 * i.

(* ---- the invariant at the CLOSE point (WVC_R_CLOSE, after the closing indent): the loop state with the node alone
   (wvc_ssN), the cursor at item n (reg 21 = n, reg 22 = 8 * n, reg 25 = 56 * n), the key slot past the last item ---- *)
Definition wvc_invC (F : wvc_fix) (P : list (list Z))
    (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
    (md0 : Model) (regs0 : bvmap 5 word)
    (W : world tfibsegs) (ms : machine_state) (mdc : Model)
    (ly : alayout) (S : astate) (U : list (Z * Z)) (buf : Z) : Prop :=
  let st := wvc_stP F P in
  let E := Ereg (ms_regs ms)
             (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F)
                (wf_keys F + 8 * wf_n F) 0) in
  wvc_at B E (wvc_ssN (wf_ty F) (wf_p F)) wvc_SH0 W ms (wvc_STK F) (wf_ot F) (wvc_FP F)
    ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U mdc (wevk (wf_cap0 F) st) /\
  wvc_sem F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st /\
  YK11.getr (ms_regs ms) 8%bv = w64 (wf_o F) /\
  YK11.getr (ms_regs ms) 9%bv = w64 (wf_v F) /\
  YK11.getr (ms_regs ms) 19%bv = w64 (wf_p F) /\
  YK11.getr (ms_regs ms) 21%bv = w64 (wf_n F) /\
  YK11.getr (ms_regs ms) 25%bv = w64 (56 * wf_n F) /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs0 3%bv /\
  YK11.getr (ms_regs ms) 4%bv = YK11.getr regs0 4%bv /\
  YK11.getr (ms_regs ms) 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) /\
  YK11.getr (ms_regs ms) 20%bv = w64 (wf_v F + 40) /\
  YK11.getr (ms_regs ms) 22%bv = w64 (8 * wf_n F) /\
  YK11.getr (ms_regs ms) 23%bv = w64 (wf_v F + 24) /\
  YK11.getr (ms_regs ms) 24%bv = w64 (wf_d F + 1) /\
  YK11.getr (ms_regs ms) 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) /\
  YK11.getr (ms_regs ms) 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) /\
  spZ (ms_regs ms) = wf_sp F - WVC_F /\
  0 < wf_n F.

(* ---- the invariant at the OPEN point (WVC_R_OPEN, after the put of '[' / '{'): the frame holds the shadow base and
   the saved registers only (wvc_ssO), the node at the resumed s1, no prelude slot yet ---- *)
Definition wvc_invO (F : wvc_fix)
    (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
    (md0 : Model) (regs0 : bvmap 5 word)
    (W : world tfibsegs) (ms : machine_state) (mdc : Model)
    (ly : alayout) (S : astate) (U : list (Z * Z)) (buf : Z) : Prop :=
  let st := wvc_stP F [if wf_ty F =? 6 then [123] else [91]] in
  let E := Ereg (ms_regs ms)
             (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F) 0) in
  wvc_at B E (wvc_ssO (wf_ty F)) wvc_SH0 W ms (wvc_STK F) (wf_ot F) (wvc_FP F)
    ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U mdc (wevk (wf_cap0 F) st) /\
  wvc_sem F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st /\
  YK11.getr (ms_regs ms) 8%bv = w64 (wf_o F) /\
  YK11.getr (ms_regs ms) 9%bv = w64 (wf_v F) /\
  YK11.getr (ms_regs ms) 19%bv = w64 (wf_p F) /\
  YK11.getr (ms_regs ms) 23%bv = w64 (wf_d F) /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs0 3%bv /\
  YK11.getr (ms_regs ms) 4%bv = YK11.getr regs0 4%bv /\
  YK11.getr (ms_regs ms) 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) /\
  spZ (ms_regs ms) = wf_sp F - WVC_F.
(* ---- the frame chain an allocator call reads at s0 = o, from the one-node clause at THIS memory ---- *)
Lemma wvc_achain : forall ly rd sp o ra nfp,
  rdword rd (o - 8) = Some ra -> rdword rd (o - 16) = Some nfp ->
  (ra < 4096 \/ nfp < alloc_ceiling) -> 0 <= ra -> 0 <= nfp ->
  sp + 16 <= o -> alloc_ceiling <= o -> o < ly_top ly - 16 -> o mod 8 = 0 ->
  exists ch, achain ly rd sp o ch /\ spine ch = (if 4096 <=? ra then [ra] else []).
Proof.
intros ly rd sp o ra nfp H8 H16 Hend Hra0 Hnfp0 Hsp Hceil Htop Hal.
destruct (Z.leb_spec 4096 ra) as [Hge | Hlt].
- assert (Hnfp : nfp < alloc_ceiling) by (destruct Hend; [lia | assumption]).
  exists [(o, ra, nfp)]. split; [|reflexivity].
  right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
    split; [lia|].
    replace (bad_next o (ly_top ly) nfp) with true; [reflexivity|].
    unfold bad_next. symmetry. apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. left.
    apply Z.leb_le. lia.
  + constructor; [cbn; lia | constructor].
- exists []. split.
  + right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [|constructor].
    cbn [fpchain]. exists ra. split; [exact H8 | lia].
  + cbn [spine map]. destruct (Z.leb_spec 4096 ra); [lia | reflexivity].
Qed.

(* ---- a read-only literal the arm puts: its bytes, their shape, and where they live, from fs_img_facts ---- *)
Lemma wvc_lit_pre : forall ly S U (W : world tfibsegs) mem md SA (LB : list Z) buf,
  fs_img_facts tfibsegs B -> AR tfibsegs B ly S W mem md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  In (SA, LB) FS_RO_STRS ->
  zbytes_at tfibsegs W mem SA LB /\ WriterSpec.bytes_ok LB /\
  wsrc_kept B tfibsegs ly S U W mem buf SA LB /\
  4096 <= SA /\ SA + Z.of_nat (length LB) <= alloc_ceiling.
Proof.
intros ly S U W mem md SA LB buf IMG HAR HRO Hin.
destruct IMG as (_ & IMG2).
destruct (IMG2 ly S W mem md HAR HRO) as (_ & _ & HSTRS & _).
rewrite Forall_forall in HSTRS.
destruct (HSTRS (SA, LB) Hin) as (HC & _). cbn [fst snd] in HC.
pose proof HC as (HCS & H4096 & Hhi & _).
destruct HCS as (HG & _).
assert (HZ : zbytes_at tfibsegs W mem SA LB).
{ unfold zbytes_at. exact (proj1 (proj1 (garr8_app tfibsegs (rdW W mem) SA LB [0]) HG)). }
split; [exact HZ|].
split.
{ unfold WriterSpec.bytes_ok. apply Forall_forall. intros c Hc.
  destruct (In_nth LB c 0 Hc) as (j & Hj & <-). exact (proj2 (HZ j Hj)). }
split; [|split; [exact H4096 | lia]].
right; right; right. exists LB. split; [exact Hin | apply Nat.le_succ_diag_r].
Qed.

End I.
