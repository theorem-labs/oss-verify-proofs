From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells.
Import ListNotations.
Open Scope Z_scope.

Definition ps_cells (f sw olen vtag vid : word) (pad : list byte) : list cell :=
  [C8 f; C4 sw; C4 olen; C4 vtag; C2 vid; CB 2 pad].

Definition pcap_byte (Fc : list byte) (i : nat) : Z := bv_unsigned (nth i Fc (Z_to_bv 8 0)).

Definition pcap_magic (Fc : list byte) : Z :=
  pcap_byte Fc 0 + 256 * pcap_byte Fc 1 + 65536 * pcap_byte Fc 2 + 16777216 * pcap_byte Fc 3.

Definition pcap_good (Fc : list byte) : bool :=
  (24 <=? Z.of_nat (length Fc)) && ((pcap_magic Fc =? 0xA1B2C3D4) || (pcap_magic Fc =? 0xD4C3B2A1)).

Definition pcap_sw (Fc : list byte) : Z := if pcap_magic Fc =? 0xD4C3B2A1 then 1 else 0.
