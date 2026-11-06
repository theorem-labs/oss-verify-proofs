(* omx-clap-core/fuzz_preset, Spec: the program live-set BOUNDS as plain numbers in MAXB, and nothing else.
   WHY THIS FILE EXISTS (a Theorem Labs lane's ruling, 2026-10-29, owner of PresetLiveSec.v / PresetGate.v, who approved this
   file): the contract texts (lib/A/PRH_FnAlloc.v and the reader / writer / tx / pj / check texts) state the live-set
   conjuncts over LSEC, L24 and DRV. PresetLiveSec.v and PresetGate.v Require lib/Prog/SlotSizes.v, which pulls six
   PLAIN contract files (check_round_trip_c, pj_set_c, put_c, round_trip_text_c, strtod_c, tx_put_c) into any file
   that Requires them; before the live-set conjuncts the kit's Require closure held ZERO lib/Prog/*_c.v. This leaf Requires
   ONLY PresetReqAt (for MAXB, whose own closure holds no *_c file), so the kit cites the bounds without that closure.
   DO NOT fold these definitions back into PresetLiveSec.v / PresetGate.v: they re-export them as notations (one term,
   so every lemma there and in CfRoomLivePreset.v applies unchanged), and the kit Requires this file only.
   The bounds themselves are proved in PresetLiveSec.v (live_sec, live_c24) and PresetGate.v (the driver's DRV);
   here they are only defined and evaluated. MAXB = 3 MiB (MAXD = 32 gives the 96). No address, no image number. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetReqAt.
Local Open Scope Z_scope.

(* the live SECONDARY requests (above the largest primary class) at any position of target_run's calls *)
Definition LSEC_A : Z := (MAXB + 96) / 1024.
Definition LSEC_B : Z := (MAXB + 96) / 1024 + (3 * MAXB + 96) / 64496 + 4.
Definition LSEC : Z := 3 + Z.max (3 * LSEC_A) (LSEC_A + 2 * LSEC_B + 2).

Lemma LSEC_value : LSEC = 9521.
Proof. vm_compute. reflexivity. Qed.

(* the live CLASS-24 requests (5,889 .. 7,936 bytes) at any position of target_run's calls *)
Definition L24_A : Z := (MAXB + 96) / 66.
Definition L24_B : Z := (MAXB + 96) / 66 + (3 * MAXB + 96) / 5872 + 4.
Definition L24 : Z := 3 + Z.max (3 * L24_A) (L24_A + 2 * L24_B + 2).

Lemma L24_value : L24 = 146219.
Proof. vm_compute. reflexivity. Qed.

(* the driver's blocks, live across every call (main's two buffers, the payload copy) *)
Definition DRV : Z := 3.
