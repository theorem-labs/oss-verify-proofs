(* reac-pw/fuzz_segconf, ASan builds: the two words of fuzz_command's contract-side vocabulary that
   the listing layer asks for (its SegRecRo / SegRecRest, the twins of fuzz_command's CmdRecRo /
   CmdRecRest). Statement text only: no function of the binary is proved here.

   Taken by path from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdRep.v at origin/ossv/recipes 501c0d516c69,
   with its module paths changed. That file has no copyright or SPDX line of its own; its head comment names its
   source as fuzz_command's released plain lib/Prog/RecInv.v read over the ASan side's reader.

   TAKEN, byte for byte: aval_mem (CmdRep.v:31-32) and in_blockA (:36-37).
   TAKEN WITH ITS IMAGE NAMES LIFTED: astr_argA (:142-153). The donor's text names five things that belong to
   fuzz_command's own image and plain proof -- LMAX (its longest recorded string), cmd_addr_b and cmd_hull_b
   (its boolean shadow checkers over its own image), cmd_ro_ends (the list of its read-only string ends) and
   RtDefs' astr_atR -- so carrying it verbatim would carry fuzz_command's image into segconf. Each is a
   parameter here, in the donor's order of use: LMAX, str_at, addr_b, hull_b, ro_ends. At
   str_at := RtDefs.astr_atR of the listing's lib/A/Rt/RtDefs, and the unit's own four values, the text is the
   donor's.
   LEFT OUT, the whole remainder of CmdRep.v: atoks_atA, acall_at, aanswer_at, areply_at and the g1_* / rep_at
   group (:40-141 and :155 to the end). They are fuzz_command's recorder state, which segconf has no
   counterpart of; segconf's own objects are in lib/A/Prog/SegABase.v (sa_rconf, sa_mconf, sa_mseg, ...).

   HOW THESE MEET SegABase's forms:
   - aval_mem IS sa_val: same body, same argument order. The bridge sa_val_aval_mem below is by reflexivity of
     the two definitions, and it holds in both directions.
   - astr_argA is NOT sa_str, and they are not interchangeable. astr_argA is over list byte, sa_str over
     SegModel's list Z; astr_argA says WHERE the string lies (one live block apart from every block of O, or
     read-only image bytes with the two boolean checkers) and bounds its length by LMAX, where sa_str says only
     that the bytes, the NUL and the slack to the next 8-byte boundary are there. segconf states the place of a
     string with sa_heap / sa_loc / sa_lit beside sa_str, and the shadow with sa_addr. A caller that holds
     astr_argA gets sa_strz's bytes from its astr_atR conjunct after mapping the byte list with
     seg_spec.zs; it does not get sa_tail, which astr_argA never asks for. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* CmdRep.v:31-32, byte for byte. Only the n-wide little-endian field read, which the recorder's layout needs
   and no runtime contract has, is defined here; where a width is 4 or 8, a contract says rd32 / rd64. *)
Definition aval_mem (rd : reader) (a : Z) (n : nat) (v : Z) : Prop :=
forall k, (k < n)%nat -> rd (a + Z.of_nat k) = Some (YG0f.le_byte v n k).

(* CmdRep.v:36-37, byte for byte: a range inside a live block (the plain proof's in_block,
   lib/Prog/joined_c.v:30-31). The harness's words are pointers into one `copy` block, not block starts, so a
   contract says this, not In (p, n) (ablocks B ly S). *)
Definition in_blockA (bl : list (Z * Z)) (a n : Z) : Prop :=
exists p k, In (p, k) bl /\ p <= a /\ a + n <= p + k.

(* astr_argA's one other donor name: fuzz_command's PLAIN lib/Prog/RecInv.v:26, byte for byte. It is
   SegABase's sa_disj with the arguments in the same order; the bridge is at the end of this file. *)
Definition iv_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
(* The five names of CmdRep.v:142-153 that belong to fuzz_command's image and plain proof, lifted so that both
   segconf images instantiate one text: the longest recorded string, the string form of the unit's runtime
   layer, the two boolean shadow checkers over the unit's own image, and the list of its read-only string
   ends. *)
Variable LMAX : Z.
Variable str_at : reader -> Z -> list byte -> Prop.
Variables addr_b hull_b : Z -> Z -> bool.
Variable ro_ends : list Z.

(* CmdRep.v:142-153, the donor's text with those five as parameters. *)
Definition astr_argA (ly : alayout) (S : astate) (rd : reader) (ro : Z -> Prop) (O : list (Z * Z))
(p : Z) (v : option (list byte)) : Prop :=
match v with
| None => p = 0
| Some x =>
  let n := Z.of_nat (length x) + 1 in
  p <> 0 /\ str_at rd p x /\ n <= LMAX + 1 /\
  ((in_blockA (ablocks B ly S) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O) \/
   ((forall i, 0 <= i < n -> ro (p + i) /\ ~ Exists (in_zr (p + i)) (as_owned_static B) /\
       ~ (as_errno B <= p + i < as_errno B + 4)) /\
    addr_b p n = true /\ hull_b p n = true /\ In (p + Z.of_nat (length x)) ro_ends))
end.
End c.
End b.

(* The bridge the image-A owner asked for: the donor's aval_mem and SegABase's sa_val are the same statement, in both
   directions, by the two definitions. *)
Lemma sa_val_aval_mem : forall rd a n v, sa_val rd a n v <-> aval_mem rd a n v.
Proof. intros rd a n v. unfold sa_val, aval_mem. split; intros H k Hk; exact (H k Hk). Qed.

Lemma sa_disj_iv_apart : forall a n b m, sa_disj a n b m <-> iv_apart a n b m.
Proof. intros a n b m. unfold sa_disj, iv_apart. split; intros H; exact H. Qed.
