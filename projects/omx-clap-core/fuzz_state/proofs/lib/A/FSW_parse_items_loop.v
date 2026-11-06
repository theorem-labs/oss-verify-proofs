(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the MEMBER LOOP of parse_items (A 0x84a04) for
   parse_items_spec k with ms <> [] - the call-site invariants, the post pi_Q, and the helpers the step files share.
   One member is four calls and four measured segments (FSW_parse_items_seg.v's header names the run lemmas):
     pi_IG  at grow (#1 at 0x84b68 for the first member, #2 at 0x84e60 for a later one)
       -> pig_call_84b68 / pig_call_84e60, segment S1f / S1          (FSW_parse_items_stG.pi_step_G)
     pi_IP  at parse_string 0x84c4c (the key)
       -> pic_call_ps_84c4c, segment S2 (keys[n] := key, `:`)         (FSW_parse_items_stP.pi_step_P)
     pi_IM  at __asan_memset 0x84d78 (the kid)
       -> pic_call_ms_84d78, segment S3                               (FSW_parse_items_stM.pi_step_M)
     pi_IV  at parse_value 0x84d98 (level k + 1)
       -> pic_call_pv_84d98, segment S4c (`,`: n + 1, the next grow)   (FSW_parse_items_stVc.pi_step_Vc)
                         or S4e (`}`: n + 1, close, ret, pi_Q)        (FSW_parse_items_stVe.pi_step_Ve)
   The entry to pi_IG [] is FSW_parse_items_entry.pi_entry; the induction over the members is
   FSW_parse_items_holds.pi_loop. The Section's variables and hypotheses are parse_items_spec's binders and premises;
   each step file repeats them verbatim.
   The invariants carry, besides the call registers and the frame: the caller's journal at the raised top ot over the
   unpoisoned memory, ARU, arodata, the heads; struct pj_in at q and the frame chain at q; the text still to read;
   the object v with its open member list (Prog/parse_items_shape.v pis_open over the live list L = slots ++ Di); the
   live list against ablocks and U (Permutation, rd_heads); the accounting rd_sum L = held T, length L <= length T, and
   g_live = live + held T for the trace T done so far, with the trace still to come in the equation
   ttrace (JObj ms) = T ++ <rest>.
   Rule 24: proves function parse_items (lookup: the CONFIRM verdict, a Theorem Labs lane's lookup/confirm-resume.md). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
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
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rd
FSW_pj FSH_Fn_reader
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_grow FSW_parse_items_calls FSW_parse_items_kit
FSW_parse_items_seg FSW_parse_items_mem FSW_parse_items_mdl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs FSW_grow_holds FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the frame chain at qq across a memory change off [qq, qq + 24) ================= *)
(* fpchain reads at bp - 8 and bp - 16 only, with s + 16 <= bp < top - 16; the reader agreement is bounded by the stack
   top (an address past 2 ^ 64 wraps, so an unbounded agreement is out of reach after a memory change) *)
Lemma pi_fpchain_kept : forall (l1 l2 : Z -> option Z) qq s top cl bp,
  fpchain l1 bp top cl -> (bp = qq \/ qq + 40 <= bp) -> s + 16 <= bp -> bp < top - 16 ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) cl ->
  (forall a, s <= a -> a + 8 <= top -> a + 8 <= qq \/ qq + 24 <= a -> l2 a = l1 a) -> fpchain l2 bp top cl.
Proof.
intros l1 l2 qq s top cl. induction cl as [|[[fp ra] nfp] cl IH]; intros bp H Hq Hsb Htp HF Hl; cbn [fpchain] in *.
- destruct H as (r & Hr & Hr2). exists r. rewrite Hl by lia. split; assumption.
- destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|? ? Hr HF']; subst. cbn [fst snd] in Hr.
  split; [reflexivity|]. split; [exact H8|]. split; [rewrite Hl by lia; exact Hra|].
  split; [rewrite Hl by lia; exact Hnfp|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  assert (Hn : bp < nfp /\ nfp < top - 16).
  { unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb1 Eb2].
    apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. lia. }
  apply (IH nfp Hrest); [| lia | lia | exact HF' | exact Hl].
  destruct Hr as [Hr | Hr]; [exfalso; congruence | right; exact Hr].
Qed.
Section CH. Context {rc : YM05.RunCeil}.
Lemma pi_chain_kept : forall (ly1 ly2 : alayout) (rd1 rd2 : reader) s qq top chq,
  achain ly1 rd1 s qq chq -> Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) chq ->
  ly_top ly1 = top -> ly_top ly2 = top ->
  (forall a, s <= a < top -> ~ (qq <= a < qq + 24) -> rd2 a = rd1 a) -> achain ly2 rd2 s qq chq.
Proof.
intros ly1 ly2 rd1 rd2 s qq top chq H HF E1 E2 Hrd. unfold achain in *. rewrite E2. rewrite E1 in H.
destruct H as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (pi_fpchain_kept (rdword rd1) (rdword rd2) qq s top chq qq H4 (or_introl eq_refl) H1 H2 HF).
intros a Ha Htp Hout. apply rdword_ext. intros j Hj. apply Hrd; lia.
Qed.
End CH.

Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- parse_items_spec k's entry, ms <> [] ---- *)
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved.

(* ================= the invariant's pieces ================= *)
(* the caller's journal from the entry, ARU, arodata, the heads *)
Definition pi_jc (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs) (memC : word -> option byte)
  (mdC : Model) (kc : Z) : Prop :=
  ajournal tfibsegs B STKt ot FP ly S W (unpoison U mem) md [] lyc Sc W1 (unpoison Uc memC) mdC kc /\
  ARU tfibsegs B lyc Sc Uc W1 memC mdC /\ arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memC) /\
  FSupoisonU.fs_heads B lyc Sc Uc.
(* the call registers every call shares, and the callee-saved list R by its values (q at atom 8, v at 20) *)
Definition pi_regsP (regsC : bvmap 5 word) (R : list (bv 5 * sv)) : Prop :=
  spZ regsC = sp0 - 144 /\ YK11.getr regsC 8 = w64 q /\ YK11.getr regsC 20 = w64 v /\
  YK11.getr regsC 3 = w64 (as_gp B) /\ YK11.getr regsC 4 = w64 (as_tp B) /\
  Forall (fun r => YK11.getr regsC (fst r) = sv_denot (Ereg regsC fs_extraT) (snd r)) R.
(* struct pj_in at q, the frame chain at q (from the entry sp0: every record lies above sp0), and the caller's window
   [sp0, ot) kept but for struct pj_in *)
Definition pi_stack (lyc : alayout) (Uc : list (Z * Z)) (W1 : world tfibsegs) (memC : word -> option byte)
  (chq : list (Z * Z * Z)) (pc : Z) : Prop :=
  achain lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) sp0 q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq /\
  ly_top lyc = ly_top ly /\
  PjIn.pj_in_ok tfibsegs (rdW W1 memC) q text len pc (dd + 1) tb /\
  wkeep tfibsegs W W1 mem memC sp0 ot q 24.
(* the text block, v, the live list L against ablocks and U, the accounting of the trace T done so far *)
Definition pi_blocks (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (L Da : list (Z * Z)) (T : list PjGrammar.ev) (peak1 : Z) : Prop :=
  rd_text tfibsegs B lyc Sc W1 memC text len tcap /\ pobj tfibsegs B lyc Sc W1 memC v /\
  rd_blocks_ok tfibsegs B lyc Sc W1 memC L /\ Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) /\
  Uc = U ++ rd_heads Da /\ Permutation Da L /\
  rd_sum L = PjGrammar.held T /\ (length L <= length T)%nat /\
  fs_glob tfibsegs W1 memC (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail /\ peak <= peak1.
(* the open object: v's header and its members so far, over the live list *)
Definition pi_obj (W1 : world tfibsegs) (memC : word -> option byte) (L : list (Z * Z)) (n kids keys cap : Z)
  (dn : list (list Z * PjTree.jv)) (Di : list (Z * Z)) : Prop :=
  PjStruct.pj_hdr tfibsegs (rdW W1 memC) v 6 0 0 kids keys n cap /\
  parse_items_shape.pis_open tfibsegs (rdW W1 memC) (ReaderRes.lin L) v true 0 kids keys cap
    (Z.of_nat (length dn)) (map snd dn) (map fst dn) Di.

(* ================= at grow: member i = length dn, (kk, x) next, rm the rest ================= *)
Definition pi_IG (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.tgo_obj i (Z.to_nat cap) ((kk, x) :: rm) /\
  (i <= Z.to_nat cap)%nat /\ 0 <= cap /\
  pi_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 (if Nat.eqb i 0 then 0x84b6c else 0x84e64) /\ YK11.getr regsC 10 = w64 v /\
  pi_regsP regsC (if Nat.eqb i 0 then pi_R0 else pi_RL) /\
  (if Nat.eqb i 0 then pi_frame0 (rdW W1 memC) sp0 xr else pi_frameL (rdW W1 memC) sp0 xr q v) /\
  pi_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    (if Nat.eqb i 0 then [] else pi_wsb pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
    concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pi_wsb pr dd ++ [125] ++ rest /\
  pi_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pi_obj W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ================= at parse_string (the key): v grown, n = length dn < cap ================= *)
Definition pi_IP (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjGrammar.EAlloc (Datatypes.S (length (flat_map PjRoundTrip.ech kk)))
    :: PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm /\
  (Datatypes.S i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  pi_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 0x84c50 /\ YK11.getr regsC 10 = w64 q /\
  pi_regsP regsC pi_RL /\ pi_frameL (rdW W1 memC) sp0 xr q v /\
  pi_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++
    concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pi_wsb pr dd ++ [125] ++ rest /\
  pi_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pi_obj W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ================= at __asan_memset (the kid) and at parse_value: the key a stored at keys[n] ================= *)
Definition pi_IK (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 a : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm /\
  (Datatypes.S i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  pi_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  pi_regsP regsC pi_RL /\ pi_frameL (rdW W1 memC) sp0 xr q v /\
  pi_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    (if pr then [32] else []) ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++
    concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pi_wsb pr dd ++ [125] ++ rest /\
  pi_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pi_obj W1 memC L (Z.of_nat i) kids keys cap dn Di /\
  PjStruct.pj_u64 tfibsegs (rdW W1 memC) (keys + 8 * Z.of_nat i) a /\
  PjStruct.pj_cstr tfibsegs (rdW W1 memC) (ReaderRes.lin L) a (Z.of_nat (length kk) + 1) kk.
Definition pi_IM dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a : Prop :=
  pi_IK dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a /\
  YK11.getr regsC 1 = w64 0x84d7c /\ YK11.getr regsC 10 = w64 (kids + 56 * Z.of_nat (length dn)) /\
  YK11.getr regsC 11 = w64 0 /\ YK11.getr regsC 12 = w64 56.
Definition pi_IV dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a : Prop :=
  pi_IK dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a /\
  YK11.getr regsC 1 = w64 0x84d9c /\ YK11.getr regsC 10 = w64 q /\
  YK11.getr regsC 11 = w64 (kids + 56 * Z.of_nat (length dn)) /\
  PjStruct.pj_zero tfibsegs (rdW W1 memC) (kids + 56 * Z.of_nat (length dn)) /\
  pobj tfibsegs B lyc Sc W1 memC (kids + 56 * Z.of_nat (length dn)).

(* ================= parse_items_spec k's post, at this entry (FSH_Fn_reader.v:414-427 verbatim) ================= *)
Definition pi_Q : world tfibsegs -> config -> Prop :=
  fun W' c' => exists D Da,
    Permutation Da D /\
    fpostU tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
      (rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms))) (U ++ rd_heads Da)
      (fun ly' S' W' regs' mem' md' =>
         YK11.getr regs' 10 = w64 0 /\
         PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len
           (p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))) (Z.of_nat k) tb /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
         Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
         rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj ms) D /\
         rd_sum D = PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj ms)) /\
         (length D <= length (PjRoundTrip.ttrace (PjTree.JObj ms)))%nat /\ pobj tfibsegs B ly' S' W' mem' v /\
         rd_text tfibsegs B ly' S' W' mem' text len tcap /\
         (exists peak', peak <= peak' /\
            fs_glob tfibsegs W' mem' (live + PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj ms))) peak'
              (cnt + Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))) fail)) W' c'.

(* ================= the entry premises (parse_items_spec k's, all of them) ================= *)
Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
(* the callees are Section hypotheses of the step files (FSW_parse_items_st*.v), not of this one *)

(* ================= small facts of the entry ================= *)
Lemma pi_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (H1 & H2 & H3 & _). unfold sp0. lia.
Qed.
Lemma pi_stk144 : 144 <= STK_parse_items (1 - k).
Proof.
assert (HF : FRAME_parse_items <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
rewrite pi_frame_val in HF. exact HF.
Qed.
Lemma pi_xr_len : length xr = 13%nat.
Proof. unfold xr. rewrite length_map. reflexivity. Qed.
Lemma pi_v_rng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
exact (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO0).
Qed.

(* ================= the resume env of a call ================= *)
(* acallee_saved of a concrete register *)
Ltac pi_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; unfold acallee_saved; lia.
(* a callee-saved register kept across a call *)
Lemma pi_kept : forall regsC regs' (r : bv 5), aregs_preserved regsC regs' ->
  acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr regsC r.
Proof. intros regsC regs' r HP Hr. exact (fsw_pres regsC regs' r HP Hr). Qed.
(* the resume env's atoms 2 / 3 / 4 / 8 / 20 / 32 *)
Lemma pi_env_at : forall regsC regs' xs R, pi_regsP regsC R -> aregs_preserved regsC regs' ->
  ew (Ereg regs' (fs_extraT ++ xs)) 8 = Z_to_bv 64 q /\ ew (Ereg regs' (fs_extraT ++ xs)) 20 = Z_to_bv 64 v /\
  ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF /\
  bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - 144 /\
  ew (Ereg regs' (fs_extraT ++ xs)) 3 = Z_to_bv 64 (as_gp B) /\ ew (Ereg regs' (fs_extraT ++ xs)) 4 = Z_to_bv 64 (as_tp B).
Proof.
intros regsC regs' xs R (Rsp & R8 & R20 & R3 & R4 & _) HP.
rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), (ew_Ereg_nat regs' _ 20 20%bv eq_refl),
  (ew_Ereg_nat regs' _ 2 2%bv eq_refl), (ew_Ereg_nat regs' _ 3 3%bv eq_refl), (ew_Ereg_nat regs' _ 4 4%bv eq_refl).
change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
rewrite (pi_kept regsC regs' 8%bv HP ltac:(pi_acs)), (pi_kept regsC regs' 20%bv HP ltac:(pi_acs)),
  (pi_kept regsC regs' 2%bv HP ltac:(pi_acs)), (pi_kept regsC regs' 3%bv HP ltac:(pi_acs)),
  (pi_kept regsC regs' 4%bv HP ltac:(pi_acs)).
unfold spZ in Rsp. repeat split; assumption.
Qed.
(* the callee-saved list R restated at the resume: each value names only q (8), v (20) and the shadow base (32) *)
Definition pi_R_ok (R : list (bv 5 * sv)) : bool :=
  forallb (fun r => negb (Z.eqb (bv_unsigned (fst r)) 0) && negb (Z.eqb (bv_unsigned (fst r)) 10) &&
    ((Z.eqb (bv_unsigned (fst r)) 9) || ((18 <=? bv_unsigned (fst r)) && (bv_unsigned (fst r) <=? 27))) &&
    forallb (fun n => Nat.eqb n 8 || Nat.eqb n 20 || Nat.eqb n 32) (pik_sv_atoms (snd r))) R.
Lemma pi_R0_ok : pi_R_ok pi_R0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_RL_ok : pi_R_ok pi_RL = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_setr_ok : forall regsC regs' xs R e10, pi_regsP regsC R -> aregs_preserved regsC regs' -> pi_R_ok R = true ->
  YK11.getr regs' 10 = sv_denot (Ereg regs' (fs_extraT ++ xs)) e10 ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r))
    ((10%bv, e10) :: R).
Proof.
intros regsC regs' xs R e10 HR HP Hok Ha0.
pose proof (pi_env_at regsC regs' xs R HR HP) as (E8 & E20 & E32 & _).
pose proof HR as (_ & R8 & R20 & _ & _ & RL).
constructor; [split; [intros E; discriminate E | exact Ha0]|].
unfold pi_R_ok in Hok. rewrite forallb_forall in Hok. rewrite Forall_forall in RL |- *.
intros [r e] Hin. pose proof (Hok _ Hin) as Hb. pose proof (RL _ Hin) as Hr. cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Hat]. apply andb_prop in Hb as [Hb Hcs]. apply andb_prop in Hb as [H0 _].
split.
- intros ->. discriminate H0.
- rewrite (pi_kept regsC regs' r HP).
  + rewrite Hr. apply pik_sv_denot_agree; [reflexivity|].
    intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
    apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
    * rewrite (ew_Ereg_nat regsC _ 8 8%bv eq_refl), R8. symmetry. exact E8.
    * rewrite (ew_Ereg_nat regsC _ 20 20%bv eq_refl), R20. symmetry. exact E20.
    * change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
      rewrite <- E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + unfold acallee_saved. apply orb_prop in Hcs as [Hcs|Hcs]; [apply Z.eqb_eq in Hcs; lia|].
    apply andb_prop in Hcs as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
Qed.

(* ================= the call premises every step needs ================= *)
(* struct pj_in's three fields as values *)
Lemma pi_pin_vals : forall m qq pc d, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  val_mem tfibsegs m qq 8 pc /\ val_mem tfibsegs m (qq + 8) 8 (text + len) /\ val_mem tfibsegs m (qq + 16) 4 d.
Proof.
intros m qq pc d H. pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ H) as (Hq0 & Hq64 & Ht0 & Hp & Hte & _ & _ & _ & Hd).
destruct H as (Bp & Be & Bd & _).
split; [apply fsw_pj_u64_val; split; [lia | exact Bp]|].
split; [apply fsw_pj_u64_val; split; [lia | exact Be]|].
apply (proj2 (fsw_pj_word4_iff tfibsegs m (qq + 16) d ltac:(lia) ltac:(lia))). exact Bd.
Qed.
(* where the text and in->p lie *)
Lemma pi_text_rng : forall lyc Sc (W1 : world tfibsegs) mx mdx memC pc d,
  AR tfibsegs B lyc Sc W1 mx mdx -> rd_text tfibsegs B lyc Sc W1 memC text len tcap ->
  PjIn.pj_in_ok tfibsegs (rdW W1 memC) q text len pc d tb ->
  4096 + HEAD <= text /\ text <= pc <= text + len /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
intros lyc Sc W1 mx mdx memC pc d HAR (Ht & Hb & Hl) HIN.
destruct (fsw_rblock_low B lyc Sc W1 mx mdx _ text tcap HAR Hb) as (_ & H2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof asan_consts as (C1 & _). lia.
Qed.
(* a live-list sum is non-negative *)
Lemma pi_rd_sum_nn : forall lyc Sc (W1 : world tfibsegs) memC L, rd_blocks_ok tfibsegs B lyc Sc W1 memC L -> 0 <= rd_sum L.
Proof.
intros lyc Sc W1 memC L. induction L as [|[a kk] L IH]; intros H; [unfold rd_sum; cbn; lia|].
unfold rd_sum in *. cbn [fold_right fst snd].
assert (Hkk : 0 < kk) by (destruct (H a kk (or_introl eq_refl)) as (_ & _ & Hk0 & _); exact Hk0).
assert (HL : rd_blocks_ok tfibsegs B lyc Sc W1 memC L) by (intros a' k' Hin; apply H; right; exact Hin).
pose proof (IH HL). lia.
Qed.
(* the live list's blocks are none of the entry's *)
Lemma pi_not_entry : forall lyc Sc (W1 : world tfibsegs) mx mdx L, AR tfibsegs B lyc Sc W1 mx mdx ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  forall b, In b (rd_hblocks L) -> ~ In b (ablocks B ly S).
Proof.
intros lyc Sc W1 mx mdx L HAR HP b Hb He.
pose proof (FSW_pj_set_heads.pSh_ablocks_nodup B lyc Sc W1 mx mdx HAR) as ND.
apply (Permutation_NoDup HP) in ND. apply (proj2 (NoDup_ListNoDup _)) in ND.
exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ ND He Hb).
Qed.
(* the old kids / keys blocks of v at a grow call: grow_spec's slot premises, from the open object *)
Lemma pi_slots_of : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC Da T peak1 n kids keys cap dn Di,
  ARU tfibsegs B lyc Sc Uc W1 memC mdC ->
  pi_blocks lyc Sc Uc W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) Da T peak1 ->
  pi_obj W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) n kids keys cap dn Di -> 0 <= cap ->
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  PjStruct.pj_slots_at (fun a kk => In (a, kk) Dold0) 6 kids keys (Z.of_nat (length dn)) cap /\
  rd_blocks_ok tfibsegs B lyc Sc W1 memC Dold0 /\ PjStruct.pj_apart Dold0 v /\
  incl (rd_heads Dold0) Uc /\ (forall b, In b (rd_hblocks Dold0) -> ~ In b (ablocks B ly S)) /\
  rd_sum Dold0 <= PjGrammar.held T.
Proof.
intros lyc Sc Uc W1 memC mdC Da T peak1 n kids keys cap dn Di HARU
  (_ & _ & HBL & HPERM & HUc & HDa & HSUM & _) (_ & HOP) Hcap0 Dold0.
assert (ES : parse_items_shape.pis_slots true kids keys cap = Dold0) by reflexivity.
assert (HIN : forall b, In b Dold0 -> In b (parse_items_shape.pis_slots true kids keys cap ++ Di))
  by (intros b Hb; apply in_or_app; left; rewrite ES; exact Hb).
pose proof HOP as (HN & HA & _ & HSL & _).
split.
{ apply (parse_items_shape.pis_slots_at_mv (ReaderRes.lin (parse_items_shape.pis_slots true kids keys cap ++ Di))
    (fun a kk => In (a, kk) Dold0) true kids keys (Z.of_nat (length dn)) (Z.of_nat (length dn)) cap HSL);
    [destruct HSL as (_ & Hc & _); lia | exact Hcap0 | intros a kk Hak; rewrite <- ES; exact Hak]. }
split; [intros a kk Hak; exact (HBL a kk (HIN _ Hak))|].
split; [intros b x Hb; exact (HA b x (HIN b Hb))|].
split.
{ intros h Hh. rewrite HUc. apply in_or_app. right. unfold rd_heads in *.
  apply in_map_iff in Hh as (b & <- & Hb). apply (in_map (fun b => (fst b - HEAD, HEAD))).
  exact (Permutation_in _ (Permutation_sym HDa) (HIN b Hb)). }
split.
{ intros b Hb. pose proof HARU as (HAR & _). apply (pi_not_entry lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks in *. apply in_map_iff in Hb as (b0 & <- & Hb0). apply (in_map (fun b => (fst b - HEAD, snd b + HEAD))).
  exact (HIN b0 Hb0). }
assert (HD : 0 <= rd_sum Di) by (apply (pi_rd_sum_nn lyc Sc W1 memC Di); intros a kk Hak; apply HBL; apply in_or_app; right; exact Hak).
rewrite pim_rd_sum_app in HSUM. rewrite ES in HSUM. lia.
Qed.
(* sums over a permutation, and over the ASan blocks of a reader list *)
Lemma pi_rd_sum_perm : forall a b, Permutation a b -> rd_sum a = rd_sum b.
Proof.
intros a b HP. induction HP; unfold rd_sum in *; cbn [fold_right] in *; lia.
Qed.
Lemma pi_rd_sum_hb : forall L, rd_sum (rd_hblocks L) = rd_sum L + HEAD * Z.of_nat (length L).
Proof.
induction L as [|[a kk] L IH]; [reflexivity|]. unfold rd_sum, rd_hblocks in *. cbn [map fold_right fst snd length] in *.
rewrite IH. lia.
Qed.
(* the budget premises of a callee whose events X come next in the trace: tr = T ++ X ++ Y *)
Lemma pi_budget : forall lyc Sc L T X Y,
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ X ++ Y ->
  st_nev Sc <= st_nev S + rd_ev T ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  rd_sum L = PjGrammar.held T -> (length L <= length T)%nat ->
  quiet (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) /\
  live + PjGrammar.held T + rd_live X < 2 ^ 64 /\
  st_nev Sc + rd_ev X <= EV_MAX /\ blocks_bytes Sc + rd_live X <= LIVE_MAX /\ rd_sizes_ok X.
Proof.
intros lyc Sc L T X Y Htr Hnev HP HS HL.
rewrite Htr in HQT, HSZ, HLIVE, HEV, HBB.
rewrite !length_app, !Nat2Z.inj_add in HQT.
apply pim_sizes_app in HSZ as [_ HSZ]. apply pim_sizes_app in HSZ as [HSZ _].
rewrite !pim_rd_live_app in HLIVE, HBB. rewrite !pim_rd_ev_app in HEV.
pose proof (pim_held_live T) as HHL. pose proof (pim_D_live L T HS HL) as HDL.
pose proof (pim_rd_live_nn Y) as HY1. pose proof (pim_rd_ev_nn Y) as HY2.
assert (BB : blocks_bytes Sc = blocks_bytes S + rd_sum L + HEAD * Z.of_nat (length L)).
{ rewrite (FSW_grow_holds.grow_bb B lyc Sc), (FSW_grow_holds.grow_bb B ly S), (pi_rd_sum_perm _ _ HP),
    pim_rd_sum_app, pi_rd_sum_hb. lia. }
split; [|split; [unfold HEAD in *; lia|split; [lia|split; [unfold HEAD in *; lia | exact HSZ]]]].
destruct (pim_quiet_split cnt fail (Z.of_nat (length T)) (Z.of_nat (length X) + Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQT) as [_ HQ2].
destruct (pim_quiet_split (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) (Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQ2) as [HQ3 _].
exact HQ3.
Qed.

(* ================= the resume: from the kit's state to a segment's start state ================= *)
(* the text bytes at in->p, read off pj_in_ok's `bytes_at text tb` and the split of rest_at *)
Lemma pi_txt_bytes : forall m qq pc d bs more, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  ReaderRes.rest_at tb text pc = bs ++ more ->
  Forall (fun c => 0 <= c < 256) bs /\
  (forall i, (i < length bs)%nat -> mbyte tfibsegs m (pc + Z.of_nat i) = Some (Z_to_bv 8 (nth i bs 0))).
Proof.
intros m qq pc d bs more HIN HR.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Bt0 & Bt1 & Bt) & _).
assert (KEY : forall i, (i < length bs)%nat -> exists b : byte, mbyte tfibsegs m (pc + Z.of_nat i) = Some b /\
  bv_unsigned b = nth i bs 0).
{ intros i Hi.
  assert (E : nth_error (ReaderRes.rest_at tb text pc) i = Some (nth i bs 0))
    by (rewrite HR, nth_error_app1 by exact Hi; apply nth_error_nth'; exact Hi).
  unfold ReaderRes.rest_at, ReaderRes.zb in E. rewrite nth_error_map, nth_error_skipn in E.
  destruct (nth_error tb (Z.to_nat (pc - text) + i)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. exists b. split; [|exact E].
  assert (Hj : (Z.to_nat (pc - text) + i < length tb)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
  pose proof (Bt _ Hj) as Hb. rewrite Eb in Hb.
  replace (text + Z.of_nat (Z.to_nat (pc - text) + i)) with (pc + Z.of_nat i) in Hb by lia. exact Hb. }
split.
- apply Forall_forall. intros c Hc. apply (In_nth bs c 0) in Hc as (i & Hi & <-).
  destruct (KEY i Hi) as (b & _ & Eb). rewrite <- Eb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. lia.
- intros i Hi. destruct (KEY i Hi) as (b & Hm & Eb). rewrite Hm, <- Eb, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* struct pj_in survives a memory change that keeps q's 24 bytes (value and writability) and the text *)
Lemma pi_pin_kept : forall m m' qq pc d, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  (forall x, qq <= x < qq + 24 -> mbyte tfibsegs m' x = mbyte tfibsegs m x /\
     (writable_at tfibsegs m x -> writable_at tfibsegs m' x)) ->
  (forall x, text <= x < text + len -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  PjIn.pj_in_ok tfibsegs m' qq text len pc d tb.
Proof.
intros m m' qq pc d HIN HQ HT.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & _ & _ & _ & _ & Hlt & _).
destruct HIN as (B1 & B2 & B3 & (W0 & W1 & W2) & H5 & H6 & H7 & H8 & H9 & B10 & Hi11 & Hi12).
assert (KB : forall a bs, Mem.bytes_at tfibsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) ->
  mbyte tfibsegs m' x = mbyte tfibsegs m x) -> Mem.bytes_at tfibsegs m' a bs).
{ intros a bs (A0 & A1 & A2) Hkp. split; [exact A0|]. split; [exact A1|]. intros i Hi.
  change (Mem.mrd tfibsegs m' (Mem.wa (a + Z.of_nat i))) with (mbyte tfibsegs m' (a + Z.of_nat i)).
  rewrite (Hkp (a + Z.of_nat i) ltac:(lia)). exact (A2 i Hi). }
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj Hi11 Hi12))))))))))).
- apply KB; [exact B1|]. intros x Hx. rewrite Mem.length_le8 in Hx. apply HQ. lia.
- apply KB; [exact B2|]. intros x Hx. rewrite Mem.length_le8 in Hx. apply HQ. lia.
- apply KB; [exact B3|]. intros x Hx. rewrite Mem.length_le4 in Hx. apply HQ. lia.
- split; [exact W0|]. split; [exact W1|]. intros i Hi.
  pose proof (W2 i Hi) as Hw. destruct (HQ (qq + i) ltac:(lia)) as (_ & Hwr). apply Hwr. exact Hw.
- apply KB; [exact B10|]. intros x Hx. apply HT. lia.
Qed.
(* a list of conditions, one per index *)
Lemma pi_conds_map : forall E (f : nat -> acond) l, (forall j, In j l -> acond_ok E (f j)) -> conds_ok E (map f l).
Proof.
intros E f l H. induction l as [|j l IH]; cbn [map conds_ok]; [exact I|].
split; [apply H; left; reflexivity | apply IH; intros j' Hj'; apply H; right; exact Hj'].
Qed.
(* the white-space loop's conditions: n white-space bytes from the cursor c0 + o, a stop byte after them, all before
   in->end *)
Lemma pi_conds_ws : forall E n o c0 e, ew E (xatom 0) = Z_to_bv 64 c0 -> ew E (xatom 1) = Z_to_bv 64 e ->
  0 <= c0 -> 0 <= o -> c0 + o + Z.of_nat n < e -> e < 2 ^ 62 ->
  conds_ok E (pi_wsc n o).
Proof.
intros E n o c0 e H0 H1 Hc0 Ho Hlt He. unfold pi_wsc.
apply pik_conds_ok_app.
- apply pi_conds_map. intros j Hj. apply in_seq in Hj. apply (pik_cond_ne E _ _ _ _ c0 e H0 H1); lia.
- cbn [conds_ok]. split; [apply (pik_cond_ltu E _ _ _ _ c0 e H0 H1); lia|].
  split; [apply (pik_cond_ltu E _ _ _ _ c0 e H0 H1); lia | exact I].
Qed.

(* ================= the shadow entries of a member-loop run ================= *)
(* the entry's stack bounds around q *)
Lemma pi_q_stack : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & _ & Hotly & _).
pose proof pi_sp0 as (_ & HceilS & _). pose proof pi_stk144.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & _ & _ & _ & _ & Hq8 & _).
lia.
Qed.

(* q's 24 bytes: the stack's zero shadow *)
Lemma pi_sh_q : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> ly_stk_lo lyc = ly_stk_lo ly -> ly_stk_hi lyc = ly_stk_hi ly ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = q ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 24).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU Hlo Hhi UB Uq.
pose proof pi_q_stack as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof asan_consts as (C1 & _).
pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b q 24 q 0 24);
  [ apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) lyc Sc Uc W1 mem1 md1 (w_H W1) q 24 HARU
      ltac:(lia) ltac:(lia)));
    exact (pi_RA_stack B lyc Sc W1 (unpoison Uc mem1) md1 q 24 HAR ltac:(lia) ltac:(lia) Hq8 ltac:(reflexivity) ltac:(lia))
  | exact UB | exact Uq | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* v's 56 bytes: pobj's range_addressable, off the shadow band *)
Lemma pi_sh_v : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> pobj tfibsegs B lyc Sc W1 mem1 v ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = v ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 56).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU HPO UB Uv. pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b v 56 v 0 56);
  [ destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr | exact UB | exact Uv | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx.
exact (fsw_pobj_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 mem1 v HAR HPO x ltac:(lia)).
Qed.
(* a window [z, z + n) of a live block's body (the text, a key slot): addressable, off the shadow band *)
Lemma pi_sh_blk : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat) P nn z lo hi,
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> FSupoisonU.fs_heads B lyc Sc Uc ->
  In (P, nn) (ablocks B lyc Sc) -> P + HEAD <= z + lo -> lo <= hi -> z + hi <= P + nn ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = z ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b lo hi).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b P nn z lo hi HARU HHD Hin H1 H2 H3 UB Uz. pose proof HARU as (HAR & _).
destruct (fsw_ablock_low B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin) as (L1 & L2 & L3).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b (z + lo) (hi - lo) z lo hi);
  [ apply (fsw_block_body_addressable B lyc Sc Uc W1 mem1 md1 P nn (z + lo) (hi - lo) HARU HHD Hin);
      unfold HEAD in *; lia
  | exact UB | exact Uz | lia | lia |].
intros x Hx. rewrite (Z.min_l lo hi H2), (Z.max_r lo hi H2) in Hx.
apply (fsw_ablock_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin x). unfold HEAD in *. lia.
Qed.

(* ================= the write windows of a resume state ================= *)
Lemma pi_awr_ret : forall E lyc Sc (W1 : world tfibsegs) mx mdx memX cs,
  AR tfibsegs B lyc Sc W1 mx mdx -> pobj tfibsegs B lyc Sc W1 memX v -> frames Sc = frames S ->
  bv_unsigned (ew E 2) = sp0 - 144 -> bv_unsigned (ew E 8) = q -> bv_unsigned (ew E 20) = v ->
  awr_ok tfibsegs B E (fsT_ret_regions 144 cs pig_rs) STKt ot FP (ablocks B ly S) (ablocks B lyc Sc) lyc []
    (frames S).
Proof.
intros E lyc Sc W1 mx mdx memX cs HAR HPO Hfr E2 E8 E20.
pose proof pi_stk144 as Hst. pose proof HWIN as (Hsq & Hq24 & _ & _ & _). pose proof pi_sp0 as (_ & HceilS & _).
unfold fsT_ret_regions, pig_rs. cbn [app].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp0 - 144 - ot);
  [reflexivity | cbn [fstk_ret YP09.r_base]; rewrite E2; lia
  | cbn [fstk_ret YP09.r_wlo]; unfold STKt; lia | cbn [fstk_ret YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
eapply awr_ok_cons_stack_off with (n := 8%nat) (d := q - ot);
  [reflexivity | cbn [pig_q_region YP09.r_base]; rewrite E8; lia
  | cbn [pig_q_region YP09.r_wlo]; unfold STKt; lia | cbn [pig_q_region YP09.r_whi]; lia |].
eapply awr_ok_cons_gen with (k := 20%nat) (b := v);
  [reflexivity | cbn [pig_v_region YP09.r_base]; exact E20 | | apply awr_ok_nil].
intros a Ha. cbn [pig_v_region YP09.r_wlo YP09.r_whi] in Ha.
assert (HFP : inFP FP a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
destruct HPO as [[((cid & pos & Hin & Hcid & Hal & H1 & H2) & _ & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
- right. right. split; [exact HFP|]. exists cid, pos. split; [rewrite <- Hfr; exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left. right. left. split; [exact HFP|]. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
Qed.

(* ================= reading the stop of a segment run ================= *)
Lemma pi_ew_extK : forall ws E K n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
induction ws as [|w ws IH]; intros E K n H; cbn [extK]; [reflexivity|].
rewrite IH by lia. apply ew_ewset_other. lia.
Qed.
Lemma pi_ed_extK : forall ws E K, ed (extK E K ws) = ed E.
Proof. induction ws as [|w ws IH]; intros E K; cbn [extK]; [reflexivity|]. rewrite IH. apply ed_ewset. Qed.
(* the registers a measured stop names *)
Lemma pi_regs_of_stop : forall E ss ms' (H : word -> bool) l, st_ok tfibsegs E ss (restrict H ms') ->
  pi_regs_are ss l = true -> Forall (fun r => YK11.getr (ms_regs ms') (fst r) = sv_denot E (snd r)) l.
Proof.
intros E ss ms' H l HS Hl. unfold pi_regs_are in Hl. rewrite forallb_forall in Hl.
apply Forall_forall. intros [r e] Hin. pose proof (Hl _ Hin) as Hb. cbn [fst snd] in *.
apply sv_eqb_eq in Hb. rewrite (st_ok_restrict_reg tfibsegs H E ss ms' r HS), Hb. reflexivity.
Qed.
(* the member loop's frame (pi_csL) read off a frame region at the stop, under an env with the resume's atoms *)
Lemma pi_frameL_of : forall E m cs', length xr = 13%nat ->
  bv_unsigned (ew E 2) = sp0 - 144 -> ew E 8 = Z_to_bv 64 q -> ew E 20 = Z_to_bv 64 v ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) 0 144 0 144 cs') -> incl pi_csL cs' ->
  pi_frameL m sp0 xr q v.
Proof.
intros E m cs' Hl E2 E8 E20 E32 EX HR Hinc.
pose proof pi_q_stack as (_ & _ & _ & Hqc & Hq47). pose proof asan_consts as (C1 & _).
assert (Hv : 0 <= v /\ v + 56 < 2 ^ 47) by (pose proof pi_v_rng; pose proof asan_consts as (C1' & _); lia).
assert (F : forall off e x, In (YP09.mkChunk off (CVal 8 e)) pi_csL -> sv_denot E e = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> val_mem tfibsegs m (sp0 - 144 + off) 8 x).
{ intros off e x Hin He Hx. exact (fsw_field E m 2 (sp0 - 144) cs' 0 144 0 144 off 8 e x HR E2 (Hinc _ Hin) He
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Hsh : forall y, 0 <= y < 2 ^ 47 -> 0 <= pi_sh y < 2 ^ 64).
{ intros y Hy. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
split.
- unfold pi_frame0. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 144 + (136 - 8 * Z.of_nat j)) by lia.
  apply (F _ (SOff (xatom (3 + j)) 0)); [| rewrite fsw_SOff0, EX by lia; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range].
  unfold pi_csL. apply in_or_app. right. unfold pi_cs0.
  apply (in_map (fun j => YP09.mkChunk (136 - 8 * Z.of_nat j) (CVal 8 (SOff (xatom (3 + j)) 0)))).
  apply in_seq. lia.
- split; [replace (sp0 - 136) with (sp0 - 144 + 8) by lia; apply (F 8 (SOff 8 8));
    [cbn; tauto | apply bv_eq; rewrite denot_SOff, E8, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia | lia]|].
  split; [replace (sp0 - 128) with (sp0 - 144 + 16) by lia; apply (F 16 (pi_shv 8 16));
    [cbn; tauto | apply pi_shv_denot; [exact E8 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  split; [replace (sp0 - 120) with (sp0 - 144 + 24) by lia; apply (F 24 (pi_shv 20 24));
    [cbn; tauto | apply pi_shv_denot; [exact E20 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  replace (sp0 - 112) with (sp0 - 144 + 32) by lia; apply (F 32 (SOff 20 32));
    [cbn; tauto | apply bv_eq; rewrite denot_SOff, E20, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia | lia].
Qed.

(* ================= a segment's start state ================= *)
(* the literal text window at the cursor is apart from the resume regions (frame, the shadow-base cells, q, v) *)
Lemma pi_treg_disj : forall E bs cs pc,
  bv_unsigned (ew E (xatom 0)) = pc -> bv_unsigned (ew E 2) = sp0 - 144 -> bv_unsigned (ew E 8) = q ->
  bv_unsigned (ew E 20) = v ->
  text <= pc -> pc + Z.of_nat (length bs) <= text + len -> len < tcap -> text + tcap <= alloc_ceiling ->
  4096 + HEAD <= text -> (text + tcap <= 0x10000 \/ FS_IMG_END <= text - HEAD) ->
  all_disjoint E (pik_treg (xatom 0) 0 bs) (fsT_ret_regions 144 cs pig_rs).
Proof.
intros E bs cs pc E0 E2 E8 E20 H1 H2 H3 H4 H5 Himg.
pose proof pi_q_stack as (_ & _ & _ & Hqc & Hq47). pose proof pi_sp0 as (_ & HceilS & _). pose proof pi_stk144.
pose proof pi_v_rng as (Hv1 & Hv2).
apply all_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pig_rs, pig_q_region, pig_v_region, pik_treg,
  extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E0, E2, E8, E20.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
  HEAD in *.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; destruct HVTX; lia.
Qed.
(* the kit's resume state, with the callee-saved registers restated, the text window added and the white-space
   conditions as facts, over any resume region list rs: the start state of S1f / S1 / S4c / S4e *)
Lemma pi_start_T : forall regsC regs' xs (W' : world tfibsegs) memX r cs rs gf R e10 bs conds,
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r 144 cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) memX (seg_rom tfibsegs))) ->
  pi_regsP regsC R -> aregs_preserved regsC regs' -> pi_R_ok R = true ->
  YK11.getr regs' 10 = sv_denot (Ereg regs' (fs_extraT ++ xs)) e10 ->
  region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' memX) (pik_treg (xatom 0) 0 bs) ->
  all_disjoint (Ereg regs' (fs_extraT ++ xs)) (pik_treg (xatom 0) 0 bs) (fsT_ret_regions 144 cs rs) ->
  conds_ok (Ereg regs' (fs_extraT ++ xs)) conds ->
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs))
    (pik_addf (pik_addr (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)) [pik_treg (xatom 0) 0 bs]) []
       conds [])
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) memX (seg_rom tfibsegs))).
Proof.
intros regsC regs' xs W' memX r cs rs gf R e10 bs conds HS HR HP Hok Ha0 RT DJ HC.
apply pik_st_ok_addf; [| exact I | exact HC | exact I].
change (pik_addr (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)) [pik_treg (xatom 0) 0 bs]) with
  (mkSS (ss_pc (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)))
     (ss_regs (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)))
     (pik_treg (xatom 0) 0 bs :: ss_mem (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)))
     (ss_resv (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)))
     (ss_facts (pik_setr (fss_retT r 144 cs rs gf) ((10%bv, e10) :: R)))).
apply st_ok_add_region'.
- apply pik_st_ok_setr; [exact HS|]. cbn [ms_regs mkst restrict].
  exact (pi_setr_ok regsC regs' xs R e10 HR HP Hok Ha0).
- apply pik_treg_wf. lia.
- rewrite restrict_mem. exact RT.
- exact DJ.
Qed.

(* ================= the members' own facts (FS_DOC_STRS, well-formedness, depth) ================= *)
Lemma pi_mem_facts_gen : forall d l, FSDocStrs.fs_doc_values (PjTree.JObj l) -> FSDocStrs.fs_doc_strings (PjTree.JObj l) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj l) -> (PjTree.depth (PjTree.JObj l) <= Datatypes.S d)%nat ->
  forall dn kk x rm, l = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\ (PjTree.depth x <= d)%nat.
Proof.
intros d l HV HS HF HD dn. revert l HV HS HF HD.
induction dn as [|[k0 x0] dn IH]; intros l HV HS HF HD kk x rm El; subst l; cbn [app] in *.
- destruct (pim_vals_cons kk x rm HV) as (V1 & _). destruct (pim_strs_cons kk x rm HS) as (S1 & S2 & _).
  destruct (pim_wf_cons kk x rm HF) as (F1 & _). destruct (pim_depth_cons kk x rm d HD) as (D1 & _).
  repeat split; assumption.
- destruct (pim_vals_cons k0 x0 _ HV) as (_ & V2). destruct (pim_strs_cons k0 x0 _ HS) as (_ & _ & S3).
  destruct (pim_wf_cons k0 x0 _ HF) as (_ & F2). destruct (pim_depth_cons k0 x0 _ d HD) as (_ & D2).
  exact (IH _ V2 S3 F2 D2 kk x rm eq_refl).
Qed.
Lemma pi_mem_facts : forall dn kk x rm, ms = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\
  (PjTree.depth x <= 2 - Datatypes.S k)%nat.
Proof.
intros dn kk x rm E. apply (pi_mem_facts_gen (1 - k) ms HDV HDS HWF ltac:(lia) dn kk x rm E).
Qed.

(* the caller's window across two steps *)
Lemma pi_wkeep_trans : forall (W1 W2 : world tfibsegs) m1 m2 s,
  wkeep tfibsegs W W1 mem m1 sp0 ot q 24 -> wkeep tfibsegs W1 W2 m1 m2 s ot q 24 -> s <= sp0 ->
  wkeep tfibsegs W W2 mem m2 sp0 ot q 24.
Proof.
intros W1 W2 m1 m2 s H1 H2 Hs a Ha Hq.
destruct (H1 a Ha Hq) as (B1 & R1). destruct (H2 a ltac:(lia) Hq) as (B2 & R2).
split; [rewrite B2; exact B1 | rewrite R1; exact R2].
Qed.
(* the fake frames across the caller's journal (own = []) *)
Lemma pi_frames : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC kc, pi_jc lyc Sc Uc W1 memC mdC kc -> frames Sc = frames S.
Proof.
intros lyc Sc Uc W1 memC mdC kc (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.

End M.
