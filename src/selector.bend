import Base
import ./keccak.bend as Keccak

# Prints the ABI selector of each signature, such as "set(uint256)".
def lines(signatures: List<String>) -> String:
  match signatures:
    case Nil{}:
      ""
    case signature <> rest:
      Keccak.hex(Keccak.selector(signature)) ++ "\n" ++ lines(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    signatures : List<String> <- IO.args()
    IO.write(lines(signatures))
