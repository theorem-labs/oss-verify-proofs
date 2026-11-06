(* The slot's top glue: lib_contract_x_T at ENTRY (the T form the frame asks, lib/Prog/LLVMFuzzerTestOneInput_c.v)
   from the SR-level pieces of the walk, each a Section hypothesis here and a lemma of its own glue file:
   - ENTRY_OK: from the entry cut (LFrEn.cut_entry) to the loop head of operation 0, the exit, or the end;
   - ARM_OK k: from the loop head of operation i with op byte % 6 = k to that of i + 1 or the exit;
   - EXIT_OK: from the exit (0x1413c) to the end (the slot's ret);
   - LH_OP: the loop head's op byte exists (it reads the payload byte at the cursor).
   The cuts are LFr.CUT; the slot's own blocks are hb (the model md, the marks mk and, when the driver call
   starts with no kept block, the FILE block the first mark opens), the kept set T. LLoop.slot_runs composes
   the pieces; LFrPo.cut_post_lib turns the end cut into the post. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LLoop LEDefs LFr LFrEn LFrPo.
Import ListNotations.
Local Open Scope Z_scope.

(* the caller's registers the slot keeps, as the entry / exit walks name them *)
Definition lg_gp (g : lghost) : word := getr (lg_regs g) 3.
Definition lg_R (g : lghost) : lregs :=
  LRegs (wz (lg_ra g)) (getr (lg_regs g) 8) (getr (lg_regs g) 9) (getr (lg_regs g) 18) (getr (lg_regs g) 19)
        (getr (lg_regs g) 20) (getr (lg_regs g) 21) (getr (lg_regs g) 22) (getr (lg_regs g) 23)
        (getr (lg_regs g) 24) (getr (lg_regs g) 25) (getr (lg_regs g) 26) (getr (lg_regs g) 27).
Definition lg_G (g : lghost) : lent := LEnt (lg_S g) (len_p0 g) (lg_pl g) (lg_gp g) (lg_R g).
Definition lg_E (g : lghost) (md mk : Z) : lenv := le_env (lg_G g) md mk.

(* the slot's own blocks: md, mk, and the FILE block when the driver call started with T = [] *)
Definition hx (g : lghost) (T : list (Z * Z)) : list (Z * Z) :=
  match lg_T g with [] => T | _ :: _ => [] end.
Definition hb_inv (g : lghost) (E : lenv) (hb T : list (Z * Z)) : Prop :=
  Permutation hb ((e_md E, MD_SIZE) :: (e_mk E, MK_SIZE) :: hx g T).

(* the end: the slot's ret, a0 = 0, the caller's registers, the long_alias NUL the GI carries *)
Definition fin_P (g : lghost) (ms : machine_state) : Prop :=
  getr (ms_regs ms) 10 = Z_to_bv 64 0 /\ regs_preserved (lg_regs g) (ms_regs ms) /\
  bytes_at rsegs (ms_mem ms) (A_LONG_ALIAS + 300) [Z_to_bv 8 0].

Section GL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).

Definition ENT (g : lghost) (c : config) : Prop := CUT B API g L_ENTRY [] (lg_T g) (lentry_ms g) c.
Definition LH (g : lghost) (i : Z) (c : config) : Prop :=
  exists md mk hb T, lenv_ok (lg_E g md mk) /\ hb_inv g (lg_E g md mk) hb T /\
    CUT B API g L_LH hb T (lh_ms (lg_E g md mk) i (lg_gp g)) c.
Definition EX (g : lghost) (c : config) : Prop :=
  exists md mk hb T, hb_inv g (lg_E g md mk) hb T /\
    CUT B API g L_EXIT hb T (ex_ms (lg_E g md mk) (lg_gp g)) c.
Definition FIN (g : lghost) (c : config) : Prop :=
  exists hb T, ((lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = [])) /\
    CUT B API g (lg_ra g) hb T (fin_P g) c.

(* what an arm reaches: the next loop head (before operation 48) or the exit, md / mk / the FILE kept *)
Definition arm_post (g : lghost) (E : lenv) (i : Z) (c : config) : Prop :=
  exists hb T, hb_inv g E hb T /\
    ((i < 47 /\ CUT B API g L_LH hb T (lh_ms E (i + 1) (lg_gp g)) c) \/
     CUT B API g L_EXIT hb T (ex_ms E (lg_gp g)) c).

(* the obligation of the arm of operation k (op byte % 6 = k) *)
Definition ARM (k : Z) : Prop :=
  forall g md mk hb T i c,
    lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T -> 0 <= i <= 47 ->
    CUT B API g L_LH hb T
      (fun ms => lh_ms (lg_E g md mk) i (lg_gp g) ms /\ lh_op (lg_E g md mk) ms k) c ->
    SR segs c (arm_post g (lg_E g md mk) i).

Definition ENTRY_OK : Prop := forall g c, ENT g c -> SR segs c (fun c' => LH g 0 c' \/ EX g c' \/ FIN g c').
Definition EXIT_OK : Prop := forall g c, EX g c -> SR segs c (FIN g).
Definition LH_OP : Prop :=
  forall E i gp ms, lh_ms E i gp ms -> exists k, 0 <= k <= 5 /\ lh_op E ms k.

(* the kept set at a cut is [] or the one FILE block (LFR's mf_gi) *)
Lemma cut_T : forall g pc hb T P c, CUT B API g pc hb T P c -> T = [] \/ exists f, T = [(f, MF_BLOCK)].
Proof.
  intros g pc hb T P c (fx' & L & A & regs & mem & md & _ & _ & HL & _).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG).
  destruct HG as [(_ & ->) | (f & _ & -> & _)]; [left; reflexivity | right; exists f; reflexivity].
Qed.

(* md and mk are the slot's own blocks and never kept: the hp side condition of cut_evt *)
Lemma hp_md_mk : forall g E hb T, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  forall t, In t [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)] -> In t hb /\ ~ In t T.
Proof.
  intros g E hb T HI HT t Ht. split.
  - apply (Permutation_in t (Permutation_sym HI)).
    destruct Ht as [<- | [<- | []]]; [left; reflexivity | right; left; reflexivity].
  - destruct HT as [-> | (f & ->)]; [intros [] |]. intros [Hf | []].
    destruct Ht as [<- | [<- | []]]; injection Hf as _ Hs; unfold MF_BLOCK, MD_SIZE, MK_SIZE in Hs; lia.
Qed.

Section TOP.
Hypothesis HENT : ENTRY_OK.
Hypothesis HARM : forall k, 0 <= k <= 5 -> ARM k.
Hypothesis HEXIT : EXIT_OK.
Hypothesis HOP : LH_OP.

(* the loop head's cut, split by the op byte *)
Lemma lh_dispatch : forall g E i hb T c,
  CUT B API g L_LH hb T (lh_ms E i (lg_gp g)) c ->
  exists k, 0 <= k <= 5 /\ CUT B API g L_LH hb T (fun ms => lh_ms E i (lg_gp g) ms /\ lh_op E ms k) c.
Proof.
  intros g E i hb T c (fx' & L & A & regs & mem & md & Ec & Hf & HL & (c0 & HP & Heq)).
  destruct (HOP E i (lg_gp g) c0 HP) as (k & Hk & HO).
  exists k. split; [exact Hk|].
  exists fx', L, A, regs, mem, md. split; [exact Ec|]. split; [exact Hf|]. split; [exact HL|].
  exists c0. split; [split; [exact HP | exact HO] | exact Heq].
Qed.

Lemma slot_arm : forall g i c, 0 <= i <= 47 -> LH g i c ->
  SR segs c (fun c' => (i < 47 /\ LH g (i + 1) c') \/ EX g c').
Proof.
  intros g i c Hi (md & mk & hb & T & OK & HI & HC).
  destruct (lh_dispatch g _ i hb T c HC) as (k & Hk & HC').
  eapply SR_mono; [exact (HARM k Hk g md mk hb T i c OK HI Hi HC')|].
  intros c' (hb' & T' & HI' & [[Hlt HN] | HX]).
  - left. split; [exact Hlt|]. exists md, mk, hb', T'. split; [exact OK|]. split; [exact HI'| exact HN].
  - right. exists md, mk, hb', T'. split; [exact HI'| exact HX].
Qed.

Lemma slot_runs_g : forall g c, ENT g c -> SR segs c (FIN g).
Proof.
  intros g c HE.
  exact (slot_runs segs (ENT g) (EX g) (FIN g) (LH g) (HENT g) (slot_arm g) (HEXIT g) c HE).
Qed.

(* THE SLOT'S OBLIGATION at this allocator, sink and FP state *)
Theorem slot_x_T : forall ra empty j, (j < 4)%nat -> ra mod 2 = 0 ->
  @lib_contract_x_T fx rc mf_shape B API SH SK llvm_G frame_RELRO (@llvm_GI B SH) (fun _ => []) j
    LLVM_ENTRY ra empty SLOT_STACK.
Proof.
  intros ra empty j Hj Hra L A regs mem md p n pl b T K Hpre HGI Htb Hnin HGimg Hfz HK.
  set (g := LGhost regs mem md L A b T p n pl j ra empty).
  assert (HV : LGV B API g).
  { split; [exact Hpre|]. split; [exact HGI|]. split; [exact Htb|]. split; [exact Hnin|].
    split; [exact HGimg|]. split; [exact Hra | exact Hj]. }
  pose proof (cut_entry B API FF g fx HV Hfz) as HC.
  change L_ENTRY with LLVM_ENTRY in HC.
  apply (SR_realizes segs _ (FIN g) _ (slot_runs_g g _ HC)).
  intros c' (hb & T' & Hcase & HCf).
  destruct (cut_post_lib B API FF g hb T' (fin_P g) c' HCf (fun ms H => H) Hcase)
    as (fx' & L' & A' & regs' & mem' & md' & T'' & Hc & Hf & Hpost & HGI').
  apply (HK (LL 0 (m_fs md) []) c').
  exists fx', L', A', regs', mem', md', T''. split; [exact Hc|]. split; [exact Hf|]. split; [exact Hpost | exact HGI'].
Qed.

End TOP.
End GL.

(* the contract, from the pieces at every allocator / FP state the frame's facts allow *)
Theorem LLVMFuzzerTestOneInput_of_pieces : forall (B : malloc_syms) (APIf : forall rc : YM05.RunCeil, AllocAPI B)
    (SH : sink_head) (SK : sink_syms),
  (forall (rc : YM05.RunCeil), @LFF rc B (APIf rc) SH SK ->
     @ENTRY_OK rc B (APIf rc) SH SK /\ (forall k, 0 <= k <= 5 -> @ARM rc B (APIf rc) SH SK k) /\
     @EXIT_OK rc B (APIf rc) SH SK) ->
  LH_OP ->
  LLVMFuzzerTestOneInput_contract B APIf SH SK.
Proof.
  intros B APIf SH SK HP HOP ra empty FFP rc fx j Hj.
  pose proof (LFF_of_plain rc B APIf mf_shape SH SK ra empty FFP) as FF.
  destruct (HP rc FF) as (HE & HA & HX).
  pose proof FFP as (_ & Hra & _).
  exact (@slot_x_T fx rc B (APIf rc) SH SK FF HE HA HX HOP ra empty j Hj Hra).
Qed.
